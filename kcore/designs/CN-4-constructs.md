# CN-4: the constructs still to build, one design

Design agent (Fable), 2026-11-16.
CN-4 is the one document every remaining stage-4 lane is briefed from.
For every unit not yet built it replaces `designs/CN-3-merged-constructs.md` (its "Annotations after U1" block included) and `findings/CN3-ADD-addendum.md`; a lane does not read either.
The decision files stay in force and may be read: `findings/HOOK-READING-decision.md`, `F1-DECISION.md`, `R1-DECISION.md`, `NONEMPTY-decision.md`, `N1-decision.md`. Where CN-4 corrects one of them (HOOK-READING §4, section 4.7 here), CN-4's text holds.

What was run for this file: one scratch file, `/tmp/claude-1000/-home-sebastiengllmt-git-workspaces-starstream-fv-inspirations-midnightntwrk-k-rust/856a81d0-94df-4ef8-8dfb-089411adeeac/scratchpad/cn4/ConfFix.lean`, from kcore-theory's package root at `8c2f206a` (decision K1).
Every other Lean block is **to run**: where one does not elaborate, or a lemma stated here is not provable, the lane stops and reports with the Lean error; it does not respell a statement, pin less, or move a hypothesis.
"Lane's to spell" marks the only freedom.

**Amendments after REVIEW-CN4 (orchestrator, 2026-11-16; they override the body below).** findings/REVIEW-CN4.md (cold, argued, not kernel-checked) found K1, EX+FR, the e3 clause side, B1b's bodies and `OpenTotal` sound, and four defects, all accepted:
- **A (K1 x F3).** `confinedAt (k+1) s` also asks that no generator of s is a function-overloaded symbol. Counterexample: `S ::= f(A)` overloaded by `f(B) [function]` keeping the result sort, `fB(X) => fB(X)`, so S is confined with no value, and Γc's model has ★ = fB(b) in S. It is part of CF-0's text. It is inert until F3 admits such symbols, and `confined_has_value` is stated with it.
- **B (OV, `ovlPatsOK`).** "Function-overloaded" was read from direct overloads only. `overloadsOK` gains: an overloading symbol lists every function in the `ovlClosure` of its overloads. The direct definition is then the whole notion. Lands in F3.
- **C.** e5-ovl-fun's row: the account prints a conditional note ("if the text's injectivity of f fails at covered arguments, the text has no model"). The reader does not decide injectivity.
- **D (F6/F4).** `#Or` / `?B` right sides are read only where the patterns bind every variable of every alternative. Otherwise they are refused `manyValuedRightSide`.

Marks. **COLD-REVIEW** on a decision: it moves or adds a pinned statement, changes what a headline's hypothesis means, or chooses between moving a pin and weakening `Γ`; a separate reviewer reads it before the unit is briefed.

## 0. Rules every brief carries

1. `⊧`, `⊧ᴵ`, `⊧ᴵP` are infix at 26, below `∧` at 35: every conjunct `A ⊧ B` is written in parentheses.
2. One principle governs every reading: **`Γ` asserts no more than K's text states.** The text is the kompiled sentences and the builtin prose (domains.md) on which the graphs of the hooked symbols rest. A statement about which elements a sort has is admitted only with the sentence that states it.
3. A reader refusal protects no theorem. `sound_hyp`, `complete_hyp`, `exact_hyp` and `consistent_of` are stated for every `c` with `coreOK`, hand-built ones included. So every exclusion a statement needs is a decided conjunct under `coreOK`; the `RefusalReason` is the message the reader prints for it. Section 5 gives both for each row.
4. Headline statements and pins do not change in a lane. The pins that move are listed in section 3.0, each under a COLD-REVIEW decision, each in the unit named there and in no other.
5. A cone declaration is edited only by the brief that owns it (section 4.1). Anything else is a STOP with a proposal.
6. `Semantics.plain` (pinned) holds every new shape out. Each unit that edits a declaration with a `₀` copy re-proves the `…_plain` lemmas at their pinned types (`eval_plain`, `evalTerm_plain`, `fails_plain`, `fnItems_plain`, `step_plain`, `prioRuleK_plain`, `notApplies_of_binds`, `applies_of_binds`, `Γc_plain`). If one cannot be proved at its type, STOP.
7. No vacuous lemma: a new lemma whose hypotheses speak of a rule or clause shape has a kernel-checked instance at that shape beside it.
8. Fixture expectations are derived from the kompiled sentence read as a matching-logic theory. What another implementation does is recorded as evidence with its name and version, never as the reason.
9. `KoreAML.den` is for patterns without variables; a pattern with binders is read by `KoreAML.denB`.
10. STAGE4-COMMON rulings 4 to 8 (cone report against `core-cone.txt`, the `Cond.bound` review cone, package files regenerated at integration, RULES line 41 validation, the `plain` argument of the generator) stand.

## 1. What is built

INT is merging the lane heads onto kcore-merge `0e4ddd03` now. "Built" below means committed in the lane tree named; "merged" is INT's to report.

| Unit | What it is | Commit | Status |
|---|---|---|---|
| U0 | shapes at defaults: `Cond`, the fields `Rule.exs/pre/post`, `Clause.aside/exs/pre/post`, `ParamSig.raw/assoc/idem`, `Lib.carriers`, `CollKind.rangeMap`, registry 9 sorts / 202 symbols, the three `…Plain` conditions | in kcore-merge `c1b90027` | built, merged |
| U1 (a, b, fix, c, RC-1) | every statement: `Step`, `NotApplies`, `StepBy`, `StepDecided`, `applies`, `ruleRight`, `prioRuleK`, `Γcl`, `Γc`, `famEx`, `famOpen`, `SoundC`, `CompleteC`, `ExactC`, `OutIs`, `FnHyp` with `OpenDecided` and `OpenLaws`, the theorems, the `₀` texts, Pins | kcore-merge `c1b90027` (cone at `68bcce20`) | built, merged |
| BASE-1 | the `…Plain` conjuncts out of `declsOK` into Tie.lean beside `sortedOK`; the generator's `plain` argument; `test/cone.py` compares declaration texts | kcore-merge `cd4909b2`, `0e4ddd03` | built, merged |
| NJ | `noJunkItem` is the text's sentence (one unfolding, no `μ`) | kcore-kinds `186b474e` | built, at INT |
| P1 + fix | B2 `#configuration` as a parameter symbol; e0 fixtures; e1 reader devices (`orSplit`, `topAsVariable`, `existsAsVariable`, `andAsEnsures`, `bottomAsEnsures`, `orBottom`, `predicateAtBool`, `andAtBool`, `vacuousLeft`); reasons `openExtent`, `manyValuedRightSide`, `setVariable`, `unheldVariable` | kcore-fix `f6f75598`, `1ac9b6e0` | built, at INT |
| R1 + fix | `ruleSorted` final (with `condOK`, `Cond.bound`); `rulesPlain` with arm C `condApart`, `r.opens.isEmpty` kept; Confined.lean (`boolValues`, `boolClosed_model`, `confinedAt_value`, `confined_value`); `test/RulesPlainArmC.lean`; fixtures e2-open-linked, e2-open-linked-bool | kcore-theory `28ae4cee`, `5111ae1f`, `a3f7a391`, `8c2f206a` | built, at INT |
| F1 B2, B1a, C1 | `Cond.bound` in `clauseSorted`; `Fails`, `exclusion`, `DecidesAt`, `PrioDecided` over `WellSortedAt cl.vars cl.leftVars`; `aside` (`Clause.Decides`, `CoherentAll`, `ClausesAgree` over competing pairs, `lowerClauses`, pin `Coherent.of_fnDet`); pins `fails_plain`, `notApplies_of_binds` restated; `non-executable` read as `aside` | kcore-symbolic `c4283575`, `2006168b`, `1fbee135` | built, at INT |
| V1 S | a user sort hooked to a library carrier: `Lib.carrier`, `dvOK` at a carrier, `toLib`/`asSort`, `paramVal` at `libArgs`, carrier clauses of `consSorts`, `collSortOK`, `carriersOK` in `paramsPlain`; e5-hooked-int | kcore-reader `6c4172cf`, `4c16f70f` | built, at INT |
| V1 c1 (part) | RANGEMAP registry and `rangeMapHooks`, unwired | kcore-reader `d9e81ef1` | built, unwired; wiring is brief V1-c1 |

The landed text of a declaration is the tree's at these commits. CN-4 writes Lean only for what is not built, and for the readings a lane cannot recover from the tree (section 2).

## 2. What stands, for a lane that has not read CN-3

### 2.1 The objects

- `Γ c = ΓSig ∪ ΓCons ∪ ΓDomains ∪ ΓColls ∪ ΓFns ∪ ΓRules ∪ ΓFallback`; `Γstep c` is the closure `∀y. •y ⊆ ⋁_r ∃x̄_r. (L_r ∧ y ∈ R_r)`; `Γcl c` holds `boolClosed c` where `c.readsConfined` and `c.litSort Srt.bool`; `Γc c = Γ c ∪ Γcl c` is the theory the statements are about.
- `Γ` states the graphs of interpreted symbols **at values only**. A model may hold elements of a sort that are no value's. A sort is **confined** where the text states that it holds its values only (`Semantics.confined`, decision K1).
- `Γ` holds no item saying a sort has an element (NONEMPTY), and no no-junk item at a constructor sort without a generator (N1, unit NJ-0). At each sort with a value it entails an element (`inhabited_of_value`).
- A rule axiom, read: at every valuation of the non-existential variables (elements of their sorts) where the left side, its conditions and `⌈∃ē. right⌉` hold and no rule of a smaller priority applies, the configuration has **some** successor in `∃ē. right`.
- `Step` gives every instance at values. `SoundC`: a model exists, and for a step by r under σ the theory entails `den x ⇒ •famEx r σ` and `den y ⇒ famEx r σ`. `CompleteC`: every successor is in a listed outcome, a value for a rule whose left side binds every variable and `famOpen r σ` for another. `ExactC`: `Step` is exactly the steps some model of `Γc ∪ Γstep` has at values.
- `FnHyp` = results exist; `[total]` functions have values; `ClausesAgree`; `MatchIndependent`; `OpenDecided`; `OpenLaws`.

### 2.2 Readings in force

| Reading | What it says | Reason | Reversal |
|---|---|---|---|
| U0-1 | all shapes were added in one unit; a field no unit uses stays, inert | each field regenerates every package | none |
| U1-1 | `NotApplies`, `RuleApplies`, `applies`, `Fails`, `exclusion`, `DecidesAt` range over the variables of the left side and the conditions, not over every variable | a repair: two sorts `A ::= f(B)`, `B ::= g(A)` have no value and a one-element model each, so a competitor with an unused variable of sort A applies in a model and never "applies" at values | `ruleSorted` refuses a rule with a variable of a sort without a value |
| U1-2 | `Step.rule` and `Eval.clause` keep `WellSorted` over every variable; `ruleSorted` asks that each variable occurs in the rule | `Step` is every instance some model realises at values | a rule the reader must read holds a variable that occurs nowhere |
| U1-4 | `Step` does not block a larger rule merely because a competitor with an undecided open condition matches | that `Step` loses a step every model has where the condition is refuted, so `ExactC` fails of it | `OpenDecided` proves undischargeable for a text that does decide the condition |
| U1-5 | the closure axiom is a part beside `Γ`, held only where a confined sort is read | an axiom added to `Γ` makes every `Γ ⊧` statement speak of fewer models | none wanted |
| D1 | `Γ` holds the text's sentence about an existential rule and nothing else; what the theory entails of an application is a family | choosing the instance as part of the interpretation makes "y is a successor" an axiom, more than the text states | `has_model_choice` cannot be proved |
| U1-3 / HOOK-READING | a law the text writes for an open generator is an axiom of `Γ` and a hypothesis on the interpretation; a package states its theorems for every H with the named obligations (section 4.7) | the law is a sentence of the text; the text does not single out the free interpretation | a text or prose that states the generator denotes the free algebra of its laws |
| IC-1 | Int has no closure axiom: Int is unconfined | domains.md:1196-1198 say what the type is hooked to and do not name its values, as 1084 does for Bool; the kompiled sentence is `\or(\top, \bottom)` | a sentence of the text that names Int's values; then `intClosed` (below) joins `Γcl`, `confinedAt 0` gains Int, in a statement unit of its own |
| F-1 | a clause's open condition variables are of confined sorts, or its conditions are closed (`OpenDecided`); there is no "largest priority" case for clauses | at values where a clause fails `ΓFallback` states the function's rest, which says no element satisfies the condition | `ΓFallback` restated to be silent there |
| RM-3 | range-map `lookup` and `find_range` off the keys are silent (the interpretation's value) | the silent criterion: no value only where the text says there is none; domains.md:526-528, 548-550 say "an exception during concrete execution", not `#False` | the criterion changes for these and `memsetBytes` together |
| OV-1, ID-1, SV-1 | replaced by decisions F1 to F3, V7, F7 of section 3 | | |

Withdrawn before U1 and not to be reintroduced without a statement unit: `stringClosed` (the prose admits surrogate literals the fixed point lacks), `genAll` / `genClosedItems` (no sentence states that a constructor sort holds only finitely built elements; the kompiled no-junk axiom is one unfolding), `intClosed`.
The text IC-1's reversal would add:

```lean
def intClosed (c : Semantics) : KoreAML.P :=
  let X : SVar := ⟨1⟩
  let one := den c (.dv Srt.int (.int 1))
  KoreAML.inhOf (sortP (c.sortName Srt.int)) ⊆⊆
    .mu X (den c (.dv Srt.int (.int 0)) ⋁
      KoreAML.appList (symP (c.symName intAdd)) [.svar X, one] ⋁
      KoreAML.appList (symP (c.symName intSub)) [.svar X, one])
```

### 2.3 Which sorts are unconfined, and why

Unconfined: the token sorts without a hook and KConfigVar; Int, String, Bytes, Float; every carrier sort; every recursive constructor sort; **every constructor sort without a generator, and every sort that reaches one** (K1); every collection sort; so K, KItem and every sort that reaches one of these.
Per kind:
- token sorts, KConfigVar: the kompiled sentence is `\or{S}(\top{S}(), \bottom{S}())`, which states nothing, and no prose names their values;
- Int: IC-1; String: the prose admits surrogate code points as literals and calls itself incomplete; Bytes, Float: no sentence stating the extent was read;
- recursive constructor sorts: the written no-junk sentence is one unfolding and does not state that elements are finitely built;
- a constructor sort without a generator: the text holds no no-junk sentence for it, and its sorted reading gives it an element no term denotes (N1);
- collection sorts: their entries are of KItem.

A sentence that quantifies over such a sort, or whose truth needs an element of it to be a value's, is true in some models of the text and false in others at the same values, and no `Step` on values is sound and exact for it.
Confined: Bool where `litSort Srt.bool`; a constructor sort with at least one generator, each generator taking arguments of sorts confined at a smaller depth. 

## 3. Decisions on the counterexample pass

### 3.0 Summary

| Finding | Decision | Pin or cone text that moves | Mark |
|---|---|---|---|
| CX-R D1 = CX-F 5 = CX-V D4 | K1: `confinedAt` asks a generator | `Semantics.confinedAt` (cone); no `rfl` pin | COLD-REVIEW |
| CX-R D2 | R-D2: the B3 arm is built only if kompile accepts the text | none | |
| CX-R D3 | R-D3: `appOK`, `ensOK` keep predicates off the high variables | none (outside the cone) | |
| CX-R D4 | R-D4: row and reason `openRight` | none | |
| CX-R D5 | R-D5: `openExtent` row loses "complement" | none | |
| CX-R D6 | R-D6: no change to `Cond.kore`; the tie is on translated patterns; one reader guard | none | |
| CX-F 1 | F1: an overloading symbol with a function overload has its functionality, injectivity and distinctness stated at uncovered arguments only | `consItemsK`, `distGuarded` (cone); two new items | COLD-REVIEW |
| CX-F 2 | F2: such a symbol stands in no pattern, by `overloadsOK` | `overloadsOK` (a conjunct of `coreOK`; its pin names it, text unchanged) | COLD-REVIEW (with F1) |
| CX-F 3 | F3: no change; closed by F1 | none | |
| CX-F 4 | F4: no `Clause.exs` unit; `?B:Bool` on a total function's right side is read by cases | none | COLD-REVIEW (new reading) |
| CX-F 5 | K1 | | |
| CX-F 6 | F6: `#Or` on an equation's right side is read as clauses only where the function is `total` | none | COLD-REVIEW (with F4) |
| CX-F 7 | F7: a set variable outside `[simplification]` stays refused; fixtures only | none | |
| CX-F 8 | F8: the clause-side texts of e3, `pre` only | `Eval`, `Fails`/`ReqFails`, `Clause.AppliesAt`, `Clause.DecidesAt`, `PrioDecided`, `clauseEquation`, `competingEquation`, `exclusion`, `clauseSorted`, `clausesPlain` (cone); no `rfl` pin | COLD-REVIEW |
| CX-V D1 | V1: named obligation `OpenTotal`, beside `OpenLaws`, outside `FnHyp` | new pinned definition `OpenTotal`; the package form; HOOK-READING §4; `[goal]` | COLD-REVIEW |
| CX-V D2 | V2: `sortOf_withHooks` restated with "no open generator" | a `kernel_rfl` lemma, not pinned | |
| CX-V D3 | V3: the reader exhibits a value without an open generator | none | |
| CX-V D4 | K1 | | |
| CX-V D5 | (CX-V has no D5) | | |
| CX-V D6 | V6: c3 is not built; `rangeMapPattern` is a first-principles row with the corrected reason | none | |
| CX-V D7 | V7: ID-1's reversal branch is a refusal `lawAxiom`; expectations reworded | none | |
| CX-V D8 | V8: `paramsPlain` bounds the shape of a `raw` parameter | `paramsPlain` (cone, lane V's) | |
| CX-V D9 | V9: the d2 rows | none | |
| CX-V D10 | V10: `valueSorts` seeds the carrier sorts | `valueSorts` (not in the statements' cone) | |
| CX-V D11 | not decided: the prose is outside the reading set (section 7) | | |
| CX-V D12 | V12: the cell cites `kore.txt:22`, sentence 186 | none | |
| shape 6 | S6: the two-rule form | none | |
| (no finding; CN-3 had prose only) | B1b's `clauseSorted` and `clausesPlain` bodies (4.5) | `clauseSorted`, `clausesPlain` (cone) | COLD-REVIEW |

No decision moves the text of `SoundC`, `CompleteC`, `ExactC`, `FnHyp`, `coreOK`, `sound_hyp`, `complete_hyp`, `exact_hyp`, `consistent_of`, `sound_at`, `complete_at`. One pinned definition is added (`OpenTotal`).

### 3.1 K1: the `confinedAt` fix (CX-R D1, CX-F 5, CX-V D4) — COLD-REVIEW

**Fix.** FaithOK.lean, replacing the body of `Semantics.confinedAt`; docstring as written; `Semantics.confined` unchanged:

```lean
/-- Confined at depth k: Bool with only literals; or a constructor sort with a generator, each of
whose generators takes arguments of sorts confined at a smaller depth. A sort without a generator
is not confined: the text holds no sentence about which elements it has. -/
def Semantics.confinedAt (c : Semantics) : Nat → Srt → Bool
  | 0, s => s == Srt.bool && c.litSort s
  | k + 1, s => c.confinedAt 0 s ||
      ((Faithful.consSorts c).contains s && !(c.gens s).isEmpty &&
        (c.gens s).all fun g => g.argSorts.all (c.confinedAt k))
```

**Reason.** A sort is confined where the text states that it holds its values only. For a constructor sort that sentence is its no-junk axiom. For a sort without a generator the text writes none; its sorted reading gives the sort an element no term denotes (N1, kernel-checked there). The landed text is true of such a sort only by the vacuous `all`, and rested on the item `noJunkItem N []`, which is no sentence of the text and which NJ-0 removes.
With the landed text and NJ-0, `confined_value` is false at such a sort, and at the R1d flip `exact_hyp` and (beside a larger rule) `sound_hyp` are false: CX-R's `go(I) => done(I) requires g(E:Empty) ==Int 1` and its `E2-OPEN-GENLESS`, CX-F's `f() => 1 requires isC(H:S)`, CX-V's `a => b requires p(X:Empty)`. With the fix each of those variables is of an unconfined sort and passes no longer by the confined arm. Where its condition also holds a bound variable the rule or clause is refused (`openRequires`). Where the condition is closed, as in all four texts, the rule passes by arm C (a clause by F-1's closed case) with `needsWitness` true, so its `CondDecided` is owed: for these texts no value satisfies the condition and the text does not refute it, so `OpenDecided` and `FnHyp` are unprovable and no theorem is stated. That is the standing F1-DECISION §7.3 fixed for `f() => 0 requires 1 ==Int 2 *Int H`: a property of the text, listed by the account as an owed fact, and `sound_at`'s `hw` asks it of a competitor.

**Checked** (`cn4/ConfFix.lean`, kernel, axioms `propext, Classical.choice, Quot.sound`):
- `confinedAtFix_le : c.confinedAtFix k s = true → c.confinedAt k s = true` (the fix accepts no sort the landed text refuses, so no admitted definition is newly admitted through it);
- `confinedAtFix_no_gens : c.gens s = [] → c.confinedAtFix k s = true → s = Srt.bool`;
- by `#eval`: on `f2-examples/emptysort.kompile.kore` the confined sorts go from `[Bool, Empty]` to `[Bool]`; on `symrule.kompile.kore` they are `[Bool]` before and after;
- by `#eval` (`cn4/ConfFix2.lean`, the flip text of 4.3 and `needsWitness` evaluated over the landed and over the fixed `confined`, on emptysort): CX-R's `r1` (`go(I) => done(g(I)) requires g(inj(E:Empty)) ==Int 1`), alone and beside a rule of priority 200, is admitted by both, with `needsWitness` false over the landed text and **true** over the fixed one; the same rule with the mixed condition `g(inj(E)) ==Int I` is admitted over the landed text and **refused** over the fixed one.

**This outcome differs from what the three CX reports wrote** ("the rule is refused `openRequires Empty`"): that holds for a mixed condition only. For a closed condition the fix moves the rule from "admitted with nothing owed" to "admitted with `CondDecided` owed", and soundness then rests on `sound_at`'s `hw` and `FnHyp`'s `OpenDecided` asking that fact, as they do for every closed condition over an unconfined sort. The cold reviewer should attack exactly this: a text where the fixed `confined` leaves `needsWitness` false, or `CondDecided` provable, while a model with an element of a generator-less sort has a step or a function value the values lack.

**Order.** Unit CF-0. It lands **before NJ-0** and **before R1d's flip**; F1 B1b starts after it. NJ-0 and the flip may then land in either order. CF-0 alone changes no accepted semantics of a package (`needsWitness` is false and `Cond.bound` is `true` on `.top` wherever `opens` is empty and `pre`, `post` are `.top`); if a package's generated text or a `decide` fact moves, STOP.

**Declarations and owner.** `Semantics.confinedAt` was no lane's (CN-3 called `confined` final). It is assigned to **lane V, brief V1-c1, unit CF-0**, because it must land in one line with NJ-0 (`consItemsK`, lane V's) and each without the other is wrong. The same unit edits the proof of `confinedAt_value` in Confined.lean (the new conjunct in the destructuring); unit NJ-0 gives `noJunkItem_mem` the hypothesis `(hg : (c.gens N).isEmpty = false)`, which the new conjunct supplies. Confined.lean was lane R's file: from CF-0 until V2 has ended it is lane V's (CF-0, NJ-0 and d1 each edit a proof in it), and lane R reads it only, R1d, R2 and R3 included (they use `confined_value`'s statement). Statements of `confinedAt_value` and `confined_value` do not change.
CF-0 also states, beside them (to run; **not a stop condition and no unit's predecessor**: no text of CN-4 uses it, and if it is not proved in CF-0 it is recorded as open):

```lean
/-- A confined sort none of whose generators is an open generator has a value. -/
theorem confined_has_value {c : Semantics} (h : c.coreOK = true) {s : Srt}
    (hs : c.confined s = true) (hr : ∀ k ∈ c.params, k.raw = false) : ∃ v, c.sortOf v = some s
```

and adds to `test/EmptySort.lean`: `c.confined sE = false`.

**Pin.** No `rfl` pin holds `confinedAt`'s body; `Rule.needsWitness`, `Clause.needsWitness` and `famOpen_values` name `c.confined` and keep their texts. The cone row of `confinedAt` changes; `core-bound.txt` (the `Cond.bound` cone) changes in that one declaration, which the unit reports.

**Reversal.** N1 is reversed to its option (a) (the named family "a sort without a generator is empty"), or a text is found in which kompile writes `\or{S}(\bottom{S}())` for such a sort; then the conjunct is not needed.

### 3.2 Lane R

**R-D2 (CX-R D2): B3 is fixture-first.**
Fix: brief P kompiles `rule <k> c(f(X:Int)) => d(X) ... </k>` (f a total function with two preimages of one value) before R3 starts. If kompile rejects it (the message of `e3-ml-rule-lhs-ceil/kompile.txt`, exit 113), the row is R-b with its `kompile.txt`, the reader keeps `functionInPattern`, and R3 has no B3 unit. If kompile accepts it, R3 builds the cut with `pre := mem s V f(X)` (not `equals`).
Reason: a row has a kompiled sentence or it is R-b. `mem` is the sentence in every model (`C[f(X)] ≡ ∃V. C[V] ∧ V ∈ f(X)`, application distributing over union); `equals` is entailed by it and equal only where f is single-valued.
Reversal: the owner names a KORE text not written by kompile that the reader must read.
Declarations: none in the cone (`rulesPlain` already admits the cut alone and refuses it beside a larger rule, CX-R `b3`, `b3+larger`, `b3x`). Owner: lane P (fixture), lane R (arm). Pin: none.

**R-D3 (CX-R D3): the `appOK` lift.**
Fix, NICells.lean, at R3:

```lean
def appOK (c : Semantics) (H : HPaths) (r : Rule) : Bool :=
  let ks := (hiVars H r.lhs).map (·.1)
  lhsOK c H r.lhs && nodupB ks && !(loVars H r.lhs).any ks.contains &&
    (match r.req with
      | none => true
      | some t => !(varOccs t).any ks.contains) && c.ovls.isEmpty &&
    !(varOccsCond r.vars.length r.pre).any ks.contains && binds r.vars.length (varOccs r.lhs)
```

and `ensOK` gains `&& !(varOccsCond r.vars.length r.post).any ks.contains`. `binds` stays.
Reason: `appOK` says the rule's application does not read the high variables; `pre.isTop` was the only thing keeping a predicate from reading them (`<lo> X </lo> <hi> Y </hi>` with `pre := equals X Y` applies in one of two low-equal configurations).
Reversal: the noninterference lemmas are restated with a predicate reading H as an obligation.
Owner: lane R (R3). Not in a cone. Pin: none.

**R-D4 (CX-R D4): a variable the right side holds under no constructor.**
Fix: a `RefusalReason` `openRight`, printed by the reader's `openRefusal` for an open or existential variable that passes no arm of `rulesPlain` and stands in the right side, the `ensures` or `post` but in no condition. Docstring: "A variable the left side does not bind, of a sort the text leaves unconfined, that the right side holds under no constructor: under a function symbol, where an element that is no value's may give a successor that is a value's; or under a collection's symbols. The detail names the variable, its sort and the symbol." Two rows in section 5: under a function or hooked symbol, R-a; under a collection's element symbol (`<m> K |-> ?V:Int </m>`), R-c naming `ctorOccs` and `rulesPlain`.
Reason: `c() => d(f(?Z:Int))`: a model with an element h and `f(h) = w`, w outside f's values at values, has the value successor `d(w)`, which `Step` lacks; no `Step` is exact. For a collection symbol no such model was shown and none was excluded (`ΓColls`'s axioms were not read): cost.
Reversal: none for the first; the second lifts when an arm "held under collection symbols" is proved from `ΓColls` (then `ctorOccs` or `rulesPlain` gains it, a named cone change).
Decided condition: `rulesPlain` (landed). Owner: lane R (R1d, with `openRefusal`). Pin: none.

**R-D5 (CX-R D5).** The `openExtent` row reads "a quantifier or `\floor` of a term over the sort s". A complement is not refused by `Cond.bound` and is read (e3-ml-rule-lhs-not); where its truth reads an unconfined sort's extent the refusal is `openRequires` (the variable is open in a competitor's condition) or `openRight`. Reversal: a complement is found that `rulesPlain` admits and whose truth reads an unconfined extent; then `Cond.bound` gains the case. Text only.

**R-D6 (CX-R D6): binder names.**
Fix: **no change** to `Cond.kore`, `Cond.binder` or `RulePres`. Three statements instead.
1. The tie of a sentence whose rule holds a binder (`exMatch`, `ex`, `all`) is stated on translated patterns, which carry no names: `tableOf` numbers the variables of a pattern in order of occurrence (`Kore/Translate.lean`, `tableOf`, `VarTable.index`), so two patterns that differ in the spelling of variables, bound or free, in one order of occurrence translate to one pattern.
2. The emitted text of such a sentence (`emit`, under the presentation's names) is not compared with the text's; the print-back check is not stated for it.
3. The reader arm that produces a binder refuses the sentence (`variableName`, detail "a variable spelled as a binder's canonical name") when a variable of the sentence is spelled `V<i>` for an index i at or above the number of the rule's variables.
Reason: `Cond.conj` is written in the pinned bodies of `famOpen`, `Rule.condK` and `Clause.condK` (Pins.lean:66, 135, 142). Giving `Cond.kore` a list of names changes those three pins and the package data of every rule, for a difference `Γ` cannot see: `Γ` uses `canonVars` only, where a binder's index is above every variable in scope.
The reader arms that produce a binder today: none in R3 or e3 except a quantifier over Bool in a condition (`openExtent` refuses every other sort).
Reversal: a fixture's tie on translated patterns fails because the text's order of occurrence differs from `Cond.kore`'s; then the presentation carries the binders' names, in a statement unit.
Owner: lane R (R3) for statement 1 and the guard. Pin: none.

**Carried, no change.** `has_model_choice` is true as pinned; its proof for `exs ≠ []` needs the value model with its transition a parameter (`Model.stdI`, `StepM`, `StepE`; `satRulesGoal` takes `hall` and `hsome`, `satStepGoal` takes `hsub`; `consistent_of` is the instance T := `StepM`). The sentence "no model file is read" held for U1 only. A rule alone with a closed condition over an arm-A variable that no value satisfies has `needsWitness` true and `CondDecided` false: `FnHyp` is stronger than needed there, not false.

### 3.3 Lane F

**F1 (CX-F 1): OV, the obligations — COLD-REVIEW.**
The text of an overload by a function (`ovlfun.kompile.kore`: 302 `functional` of f, 303 "no confusion same constructor" of f, 304 "no confusion different constructors", 360 the overload equation `f(inj x̄) = inj(g(x̄))`) states f total, injective and apart from the other constructors at every argument, and equal to `inj ∘ g` at covered arguments. Where g is not injective (`+`), or partial, the text has no model.
The choice forced: (a) `Γ` holds all four and a new conjunct of `FnHyp` (`OvlApart`) says g is total, injective and apart at covered arguments: a pin moves, and no theorem exists for the common case; (b) `Γ` holds 302, 303, 304 at uncovered arguments only, and 360.
**Fix: (b).** For an overloading symbol one of whose overloads is a function of `c.fns` (below: a *function-overloaded* symbol), `consItemsK` writes:
- `funUncItem`: `x̄ ∈ ⟦s̄⟧ ∧ uncovered(x̄) → ∃y:N. f x̄ = y`, in place of `funItem`;
- `injUncItem`: `x̄, ȳ ∈ ⟦s̄⟧ ∧ uncovered(x̄) ∧ uncovered(ȳ) → (f x̄ = f ȳ → x̄ = ȳ)`, in place of `injItem`;
- `distUncItem` (landed) for **every** pair with another generator, in place of `distItem`: `distGuarded g g'` is true when g or g' is function-overloaded;
- `ovlEqItem` for each overload, as today.

```lean
-- Kore/Gamma.lean, after `distUncItem` (to run)
/-- Cons-Fun at uncovered arguments (`covs`: the argument sorts of the generator's overloads). -/
def funUncItem (N : String) (g : Gen) (covs : List (List String)) : Item :=
  let n := g.argSorts.length
  let x := xs 0 n
  let y : EVar := ⟨n + 1⟩
  let z : EVar := ⟨n + 2⟩
  { label := s!"cons-fun-uncovered {genName N g}", rule := "Cons-Fun-Unc", names := names "x" n ++ ["y"]
    pat := guarded (memGuards x g.argSorts ++ [uncoveredP g.argSorts covs x z])
      (sExists y (sortP N) (genPat N g (x.map .evar) ≡ .evar y)) }

/-- Cons-Inj at uncovered arguments. -/
def injUncItem (N : String) (g : Gen) (covs : List (List String)) : Item :=
  let n := g.argSorts.length
  let x := xs 0 n
  let y := xs n n
  let z : EVar := ⟨2 * n + 1⟩
  { label := s!"cons-inj-uncovered {genName N g}", rule := "Cons-Inj-Unc", names := names "x" n ++ names "y" n
    pat := guarded (memGuards x g.argSorts ++ memGuards y g.argSorts ++
        [uncoveredP g.argSorts covs x z, uncoveredP g.argSorts covs y z])
      ((genPat N g (x.map .evar) ≡ genPat N g (y.map .evar)) ⇒
        conjList ((x.zip y).map fun (a, b) => .evar a ≡ .evar b)) }
```

In `consItemsK`, with `fnOvl g := (ovlArgs g).isSome && g is function-overloaded` (lane's to spell from `c.lookupOvl` and `c.fns`): the `funItem` and `injItem` lines map each generator to its `…UncItem` with `covs := (ovlArgs g).getD []` where `fnOvl g`, and to the landed item otherwise. `covs` lists every overload's argument sorts, constructor overloads included (at those the dropped instances follow from the overload equation and the covering constructor's own items).
`EvalTerm` gains the case: an application of a function-overloaded symbol at values a function overload g covers has the result of `Eval` of g at the uninjected arguments, injected into f's result sort, `none` where that is `none`; `EvalTerm.ovl` (the `norm` case) takes the premise that no function overload covers the arguments; `norm` leaves a function-covered application alone; `ovlOver`'s lookup reads the functions' signatures too (lane's to spell; the statement of each is fixed here).
The account prints, for each function-overloaded symbol, a **text note** `overloadFunction`: the sentences (functional, no-confusion same constructor, each no-confusion pair) read at uncovered arguments only, and the sentence "at covered arguments these sentences hold in a model only if the covering function is total there, injective there and apart from the other generators; where it is not, the text itself has no model". It is a note, not an owed fact.
**Reason.** Each written item is the text's sentence restricted to fewer arguments, so the sentence entails it: the class "a named weakening that the sentence entails". (a) keeps `Γ` as strong as the text and pays with a pin and with every theorem for a non-injective overload; under (a) a contradiction of the text (the constructor axiom kompile writes for a symbol it also equates to a function) becomes a contradiction in `Γ` that `coreOK` and `FnHyp` do not see unless the pin moves. (b) moves no pin, leaves `Γ` with a model wherever the functions' own equations have one, and gives `sound_hyp`, `complete_hyp`, `exact_hyp` for the fixture. What (b) gives up: `Γ` does not refute a text whose overload contradicts 303; the note says so for the text at hand.
Why all three items and not injectivity alone: with `funItem` kept, a g undefined at a covered argument gives `f(inj x) = ⊥` beside "f total", no model, with `FnHyp` true (g need not be declared total).
**Reversal.** A proof that needs f's injectivity or totality at a covered argument; or the owner prefers `Γ` to refute such a text, which is (a): then `OvlApart` joins `FnHyp` in a statement unit.
**Declarations and owner.** `consItemsK`, `distGuarded` (lane V's and no lane's): assigned to **lane F, brief F3**, which starts after V2 has left `consItemsK`. New: `funUncItem`, `injUncItem` (F3). `EvalTerm`, `norm`, `ovlOver`, `OvlSig`, `overloadsOK`: lane F.
**Pin.** None moves. `Semantics.plain` already holds "no overloading symbol overloads a function", so `eval_plain` and the `₀` texts are untouched for a plain definition. To run at F3, for the fixture's semantics: `c.coreOK = true`, `FnHyp c`, `Consistent c`.

**F2 (CX-F 2): a function-overloaded symbol in a pattern — COLD-REVIEW (with F1).**
Fix: `overloadsOK` gains the conjunct "no function-overloaded symbol is applied in a rule's left side, a clause's patterns, or the pattern of an `exMatch` of any `pre` or `post`":

```lean
-- FaithOK.lean (to run); `c.fnOvlSyms : List Sym` the function-overloaded symbols (lane's to spell)
def Semantics.ovlPatsOK (c : Semantics) : Bool :=
  let bad := fun (t : Term) => (symOccs t).any c.fnOvlSyms.contains     -- `symOccs`: the applied symbols of a term
  c.rules.all (fun r => !bad r.lhs && (condPats r.pre ++ condPats r.post).all (!bad ·)) &&
  c.fns.all fun f => f.clauses.all fun cl =>
    cl.pats.all (!bad ·) && (condPats cl.pre ++ condPats cl.post).all (!bad ·)
-- `overloadsOK := (landed text) && c.ovlPatsOK`
```

The reader prints `functionInPattern` (landed reason: matching it needs what the function's inverse says).
Reason: `patCtxAll` holds `c.ovlSigs`, so `ruleSorted` admits the pattern; `PatVal.ovl` matches `norm`'s value, which is never the raw covered application, while in every model `f(inj x̄) = inj(g(x̄))`: `complete_hyp` is false for `run(cap(G)) => done(G)` and `sound_hyp` beside an `[owise]` rule. Reading `Eval` inside `PatVal` would put `PatVal` in the `Eval` block under `Holds.exSome`'s `↔`, which is not strictly positive.
Reversal: the B3 cut is built (R-D2) and a definition needs the pattern; then it is read as the cut, `c(V)` with `pre := mem s V f(P̄)`, and the conjunct is narrowed.
Owner: lane F (F3). Pin: `coreOK`'s pin names `overloadsOK`; its text does not move.

**F3 (CX-F 3): result-sort-keeping overloads.** No change beyond F1: under (b) no injectivity or distinctness item speaks of a covered application, so `capGas(inj z) = capN(z) = inf` contradicts nothing in `Γ`; the note of F1 says the text has no model there. `ovlPairOK` keeps `c.le kg.result o.sig.result`. Reversal: F1's.
Also stated, since CN-3 did not: an overload axiom whose larger symbol is itself a function stays refused `overloadAxiom` (the equation would be one more equation of that function, outside its clauses).

**F4 (CX-F 4): EX — COLD-REVIEW (new reading).**
Fix: there is **no** `Clause.exs` unit. `clausesPlain` keeps `cl.exs.isEmpty` for good, `Eval.ensFails` and `clauseEquation` keep their landed texts, and the field stays inert (U0-1).
An equation `f(P̄) => rhs[?B] ensures E[?B]` with one existential variable `?B:Bool`, of a function declared `total`, in a definition with `litSort Srt.bool`, is read by the reader **by cases** (device `existsAsCases`): the alternatives `(rhs[true], E[true])` and `(rhs[false], E[false])`, as clauses in F6's form. Every other existential equation is refused `existentialEquation s` (section 5).
Reason: the sentence is `premise → f(X̄) = ∃B:Bool. (rhs ∧ ⌈E = true⌉)`. With `boolClosed` (in `Γcl`: the clauses below have a `pre`, so `readsConfined`) the elements of Bool are the two literals, so the right side is `(rhs[true] ∧ ⌈E[true]⌉) ∨ (rhs[false] ∧ ⌈E[false]⌉)`: an `\or` of two alternatives, which is F6's construct. CX-F's kernel counterexample (`f() => ?B ensures ?B` has the results `some true` and `none`) is of the design that kept one clause with `exs`; it does not arise, since no clause has `exs`. The repair CX-F proposed (a binder in `clauseEquation`, "no value" as "every extension fails") is right as a theory and is not taken: it also needs `Coherent`'s result disjunct and `FnSolves` to read the family of instances, which are hypotheses of the pinned headlines, for a construct the cases already state.
Fixture expectation, from the sentence: `syntax Bool ::= f(Bool) [function, total]`, `rule f(X) => ?B ensures ?B ==Bool notBool X`: `Eval f [true] (some false)` and no other result; `FnHyp` holds. The Int form (`?Z *Int 2 ==Int X`) prints `existentialEquation Int`. Without `total` it prints `existentialEquation Bool` with the detail of F6.
Reversal: the fixture shows kompile rejects `?B` in a function rule (R-b), or writes another sentence. For a wider reading (a confined constructor sort, by enumerating its values; or a function not declared total): a definition that needs it, then a design unit of its own with a counterexample pass.
Owner: lane F (F2), reader only. Pin: none.

**F6 (CX-F 6): FR — COLD-REVIEW (with F4).**
Fix: `f(P̄) => t₁ #Or … #Or tₙ [requires R] [ensures E]` is read as clauses **only where `f.total`**; otherwise it is refused `manyValuedRightSide` with the detail "the sentence gives the function every element of each side; the function is not declared total, so where the sides differ that is more than one element, which no clause states".
The reader first distributes `\or` over applications on the right side (an application distributes over union at every symbol), giving alternatives `a₁ … aₘ`; more than 8 alternatives is refused `manyValuedRightSide` (cost). With `Eₖ` the `ensures` of alternative k (the equation's own for FR; `E[b]` for F4), the n+1 clauses, all of the equation's priority, `aside` flag, patterns and `requires`:
- for each k: `pre := and (ceil s aₖ) (equals Srt.bool Eₖ true)` (the second conjunct only with an `ensures`), `rhs := aₖ`, `ens := none`;
- one more: `pre := ⋀ₖ not (preₖ)`, `rhs := a₁`, `ens := some (.dv Srt.bool (.bool false))`.
Reason: the sentence is `premise → f(X̄) = ⋁ₖ (aₖ ∧ ⌈Eₖ⌉)`. The clause equations say `preₖ → f = aₖ` and "none defined → f = ⊥". They entail the sentence always, and the sentence entails them exactly with f's `functional` sentence (`∃y. f(X̄) = y`): then the union is one element and each defined alternative is it. kompile writes that sentence only for a `total` function. Without it the text has a model where `f(x)` is both elements (an application denotes a set; nothing in the text says a function symbol has at most one element), and the clauses' `Γ` has none: `Γ` would assert more than the text.
The last clause is needed: without it `Eval.rest` and `ΓFallback` state the interpretation's value where the sentence says ⊥ (CX-F checked it against `Eval.rest`, `ΓFallback` and `aside`).
Tie: each clause equation is a consequence of the translated sentence and f's functional sentence (for F4, with `boolClosed`).
`\top`, `\not` and an `\exists` not of F4's shape on an equation's right side stay `manyValuedRightSide`.
Reversal: an owner ruling that `function{}()` on a symbol declaration states "at most one element" (then `Γ` gains that item for every function, a statement unit, and the split is exact everywhere); or a definition that needs a non-total function's `#Or`, which needs one clause carrying alternatives (`Clause`, `clauseEquation`, `Eval.clause`: R-c).
Fixture `e3-ml-eq-rhs-or`, corrected: `h(X) => f(X) #Or g(X)` with `h` total: where f and g agree, that value; where one is undefined, the other's; where both are defined and differ, `Eval` has both results, `¬ FnDet`, and `Γ` has no model, as the text has none (h total); where neither is defined, `Eval h [x] none`, so `FnHyp`'s second conjunct is false. Without `total` on h: refused `manyValuedRightSide`.
Owner: lane F (F2), reader only; needs `Clause.pre` (e3). Pin: none.

**F7 (CX-F 7): SV-1.**
Fix: no unit. Every set variable outside a `[simplification]` axiom stays refused `setVariable` (landed). Brief P adds two fixtures that record what kompile writes or that it rejects the text: a linear one (`rule w(@S) => @S`) and a non-linear one (`rule f(@S, @S) => r`), each with `kore.txt` or `kompile.txt`.
Reason, per form:
- the `\in` form `X0 ∈ @S → w(X0) = @S` (what kompile is reported to write, TICKETS "P1 RETURNED") equates `w(x)` with every set holding x: at a sort with two elements it has no model. Reading it at singletons is a weakening the sentence entails, of a sentence that is itself contradictory; the refusal says so (R-a; detail "the sentence states the function's value for every set holding the argument").
- non-linear, either form: off the diagonal the sentence bounds the value and does not fix it; `Γ` must state nothing there and `Eval` must have no result, and the landed block has no such thing (a clause fails, and then `Eval.rest` and `ΓFallback` state the rest, or applies). A guard would be a field of `Fn` read by `Eval.rest` and `ΓFallback` (R-c naming those three).
Reversal: a fixture shows the direct form `w(@S) = r[@S]` for a linear variable; then the reader reads `@S` as an element variable (an equivalence: applications extend pointwise to sets), a reader-only unit. For the non-linear case: a definition that needs it, and the guard designed with the fixture's sentence in hand.
Owner: lane P (fixtures). Pin: none.

**F8 (CX-F 8): the clause side of e3 — COLD-REVIEW.**
Fix: e3 admits `Clause.pre` and nothing else for clauses: `clausesPlain` keeps `cl.post.isTop` and `cl.exs.isEmpty` (no reader arm produces a clause `post`; F4 and F6 need `pre` only). The texts are in brief e3 (section 4.9). `FnSolves` and `PrioDecided` are assigned to lane F.
Reason: `Fails`, `Clause.DecidesAt`, `clauseEquation`, `competingEquation` and `exclusion` read `req` only; admitting `pre` without them, FR's first clause states `h(X) = f(X)` with no premise, and a clause with `pre` false blocks nothing in `Eval` yet is excluded nowhere in `Γ`.
Reversal: a reader arm needs a clause `post`; then `Eval.postFails` and the right side of `clauseEquation` are a further unit.
Pin: no `rfl` pin; `FnHyp` and `consistent_of` name `ClausesAgree`, `MatchIndependent`, `FnSolves`, which read `Clause.AppliesAt` and `Clause.DecidesAt` by name. For a clause with `pre = .top` every edited text is the landed one.

### 3.4 Lane V and lane P

**V1 (CX-V D1): `OpenTotal` — COLD-REVIEW.**
Fix: a named obligation beside `OpenLaws`, outside `FnHyp`, a hypothesis of the package statements where `ParamsTotal` sits today.

```lean
-- Faithful.lean, after `OpenLaws` (to run)
/-- The interpretation gives each open generator a value at every argument list of its sorts:
the text's `functional` sentence for it, at values. -/
def OpenTotal (c : Semantics) : Prop :=
  ∀ k ∈ c.params, k.raw = true → ∀ vs, c.sortsOf vs = some k.sig.args →
    (c.paramVal k.sig.name vs).isSome = true

theorem openTotal_of_plain {c : Semantics} (h : ∀ k ∈ c.params, k.raw = false) : OpenTotal c
theorem openTotal_none (c : Semantics) (h : c.coreOK = true) : OpenTotal (c.withHooks HookParams.none)
theorem openTotal_lawHooks (c : Semantics) (h : c.coreOK = true)
    (hl : ∀ k ∈ c.params, (k.raw && k.assoc && k.idem) = false) (H : HookParams) :
    OpenTotal (c.withHooks (lawHooks c H))
```

`Definition.totalParams` leaves the `raw` parameters out (`ParamsTotal` is false at `HookParams.none` for a parameter with an argument, and reads `c.sortOf`, not the sort at H). A package with an open generator states each theorem for every H with `OpenLaws (d.sem.withHooks H)` **and** `OpenTotal (d.sem.withHooks H)`; section 4.7 gives the sentence. `Γ` gains no functionality item for an open generator. The reader classifies the generator's `functional` axiom "stated at values, under `OpenTotal`".
Reason: the text writes `functional` for the generator (e2-comm-ctor `kore.txt:18`, `:24`). d1's `Γ(H)` holds `f(vs) ≡ ⊥` wherever `paramVal f vs = none`, and `OpenLaws` holds there with both sides undefined; so at an H that gives the generator an ill-sorted answer the package would state its theorems about a theory that says what the text refutes. An interpretation the text admits is one under which every sentence of the text that reads H holds at values (HOOK-READING §0.4); the `functional` sentence is one of them. No pinned theorem is false without it: the obligation narrows the class of interpretations the package speaks of to the text's.
Why not the sentence inside `Γ`: then `consistent_of` needs the hypothesis and a pin moves, for the same class of interpretations.
Reversal: the owner prefers the sentence inside `Γ` (a functionality item for the open generator and a hypothesis of `consistent_of`).
Owner: lane V (V2, unit d1). Pin: `OpenTotal` is added to Pins.lean by `rfl` against its body, in V2; nothing else moves. `[goal]`: section 6.

**V2 (CX-V D2): `sortOf_withHooks`.**
Fix: under d1 `sortOf` reads `c.hooks` at an open generator. Params.lean's `kernel_rfl Semantics.sortOf_withHooks` and ParamsTotal.lean's `sortsOf_withHooks` become theorems:

```lean
theorem Semantics.sortOf_withHooks (c : Semantics) (H : HookParams)
    (hr : ∀ k ∈ c.params, k.raw = false) : (c.withHooks H).sortOf = c.sortOf
theorem Semantics.sortsOf_withHooks (c : Semantics) (H : HookParams)
    (hr : ∀ k ∈ c.params, k.raw = false) : (c.withHooks H).sortsOf = c.sortsOf
/-- A value that applies no open generator has its sort at every interpretation. -/
theorem Semantics.sortOf_withHooks_rawFree (c : Semantics) (H : HookParams) {v : GroundTerm}
    (hv : c.rawFree v = true) : (c.withHooks H).sortOf v = c.sortOf v
```

V2's brief lists and re-proves the readers (`ParamsTotal.withHooks`, two `simp` sets in ParamsTotal.lean, ten places in LibAdmitted.lean, the tests Ensures, FallbackFns, FloatFieldOne, GenFns, Guards, SilentPoints, SilentTotal, TieEns, UserProjection) and checks every other `kernel_rfl …_withHooks` lemma whose body reaches `sortOf`.
Reason: the alternative, a `sortOf` that does not read H, makes every raw application a value at every H; at an idempotent H the graph `or(x, x) ≡ x` then sits beside the distinctness of two values, and `Γ` has no model.
Consequence for expectations: `Config (c.withHooks H)` is a different set at each H; an expectation "at the configuration x" over several H names an x with `rawFree`.
Reversal: none found. Owner: lane V (V2). Pin: none (neither lemma is in Pins.lean).

**V3 (CX-V D3): the narrowed `unheldVariable`.**
Fix: the reader reads shapes 1 to 3 (and the `requires` case of S6) at a sort S only with an **exhibited value that applies no open generator**: a ground term v built from constructors, injections and literals with `d.sem.sortOf v = some S`. Otherwise `unheldVariable`. The tie lemma is `inhabited_of_value` at `(c.withHooks H).sortOf v = some S`, which `sortOf_withHooks_rawFree` gives at every H.
Reason: at a sort whose only values apply an open generator (`syntax B ::= A "&" A`), the value at `HookParams.none` is no value at an H that answers the generator ill-sorted, B is empty in every model of `Γ(H)`, and the read rule is not entailed by the sentence there. Brief P cannot wait for V2's `OpenTotal`; a value without an open generator is a value at every H.
Not taken: `value_of_openTotal` (a value at `none` gives one at every H with `OpenTotal`), which would read the shapes at such a B too. Reversal: a fixture needs it.
Owner: lane P (reader; the test is trivially met until d2, since no open generator is read before it); lane V (V2) for the lemma. Pin: none.

**V6 (CX-V D6): V3 (c3) is a refusal.**
Fix: c3 is not built. `rangeMapPattern` stays, as a first-principles row, with the reason: "a range-map symbol binding a variable in a left side: the range's bounds are of KItem (`RangeMap:Range(KItem, KItem)`), the entry's value of KItem and the rest of RangeMap, all unconfined; and the entry symbol at a range that is empty, inverted or not of Ints is silent, so at an element that is no value's the text says nothing of it". Its docstring is corrected by brief V1-c1.
Decided condition: `patternHooks` and `collPatternHooks` hold no range-map symbol, so `patCtxAll` does not sort such a pattern and `ruleSorted` is false; brief V1-c1 does not add the range-map symbols to either list.
Reason: confining Int (IC-1's reversal) does not confine what the pattern reads. CX-V's model: the rule `<k> m(([A, B) r|-> V) Rest) => V </k>` at `m([0,2) r|-> a)`, an element j of KItem that is no value's, `[5, 3) r|-> j` interpreted as `[0,2) r|-> a`; no premise forbids it, and the successor j is in no listed value.
Reversal, all four together: (a) the 3.2 statement unit has landed (`intClosed` in `Γcl`, `c.confined Srt.int`); (b) the pattern's bounds are declared Int and the entry's value and rest are held elsewhere under constructors or confined; (c) the axioms by extension are written with the guard `A <Int B` and through `in_keys` (`in_keys(K, .RangeMap) = false`; `A <Int B → in_keys(K, [A,B) r|-> V) = (A <=Int K andBool K <Int B)`; `A <Int B ∧ A <=Int K ∧ K <Int B → lookup([A,B) r|-> V, K) = V`; two range maps are equal where `in_keys` agrees at every Int key and `lookup` agrees on the keys; no axiom for `lookup(.RangeMap, K)`, which is silent by RM-3); (d) expectations say "the matches with `A <Int B`". Or the entry symbol at an improper range is decided to have no value (not silent); then (b) reduces to Int-declared bounds.
Owner: text; lane V for the docstring. Pin: none.

**V7 (CX-V D7): ID and ID-1.**
Fix. Reading ID-1: an `[idem]` axiom `\equals(f(K, K), K)` is classified by its symbol's kind:
1. f the concatenation of a set collection: `setIdempotence`, unread (landed);
2. f an open generator (no `constructor`, no `function`, no hook, `functional`, listed in its sort's no-junk axiom): `openLaw (idem)`, read; the axiom is in `Γ`, `OpenIdem` in `OpenLaws`, `lawHooks` merges equal adjacent arguments;
3. anything else, **including a symbol that kept `constructor`**: refused `lawAxiom`; nothing is added to `Γ`.
The reversal branch of CN-3 ("the constructor with the axiom in `Γ` and no model") is withdrawn.
Reason for 3: a `c` with the axiom beside the constructor axioms passes `coreOK` (no parameter is `raw`) and `OpenLaws`, and `Γ` has no model when the sort has a second constructor (`f(x, x) = x` against the distinctness of f and x): `consistent_of` would be false. The text has no model either; that is recorded on the upstream list, and the refusal's detail says it ("idempotence of a constructor contradicts its no-confusion axioms").
Expectations for `e2-idem-ctor`, placed by HOOK-READING's rule:
- for every H with `OpenLaws` and `OpenTotal`: `x | x` is `x` (the axiom states it);
- at `lawHooks`: `(x | y) | y` is a value distinct from `x | y` (the text leaves it open; true of the free interpretation);
- at `HookParams.none`: `OpenIdem` fails at `x` (`paramVal or [x, x]` is the raw application, a value other than `x`).
The clause "unless `assoc` is also written" is deleted: with both laws the generator is refused `openLaw (assoc, idem)`.
Reversal: `consistent_of` gains a hypothesis about a constructor's law (an owner decision).
Owner: lane V (V2, unit ID); the refusal is lane P's (P2). Pin: none.

**V8 (CX-V D8): the shape of a `raw` parameter.**
Fix: `paramsPlain` after V2 (final body):

```lean
def Semantics.paramsPlain (c : Semantics) : Bool :=
  c.params.all (fun k =>
    if k.raw then k.impl.isNone && !(k.assoc && k.idem) &&
      (!(k.assoc || k.idem) || k.sig.args == [k.sig.result, k.sig.result])
    else !k.assoc && !k.idem) && c.carriersOK
```

Reason: `consistent_of` is pinned for every `c` with `coreOK`. A `raw` parameter with `impl = some g` has its raw application a value beside the hook's graph value, apart below KItem: no model. A law on a `raw` parameter whose signature is not `[s, s] → s` has `OpenAssoc`/`OpenIdem` read at arguments `ΓDomains` writes no graph for. Both are suspected, not shown; the conjunct refuses shapes no text of the corpus or fixtures has, so it costs nothing.
Reversal: a fixture with such a shape; then `consistent_of` is proved for it or the model's failure shown.
Owner: lane V (V2). Pin: none.

**V9 (CX-V D9): the d2 rows.** Section 5 carries them; brief P2 implements them. In short: the generator's `functional` axiom is "stated at values, under `OpenTotal`"; a law axiom on a `function` production that is no collection concatenation stays `lawAxiom`; an open generator whose result sort is no constructor sort is refused `openGenerator` with the detail "its result sort is no constructor sort" (decided: `genWf`); `comm` has no sentence and no row beyond that statement; `openGeneratorPattern` is one row with two reasons. Owner: lane P (P2). Pin: none.

**V10 (CX-V D10): a carrier sort has values.** Fix: `Semantics.valueSorts`'s seed gains `c.lib.carriers.map (·.1)`; `valueless`'s docstring is unchanged and becomes true of a carrier sort. Reason: a carrier sort has its carrier's literals (`dvOK`); the account prints "sorts without a value: MyInt" for e5-hooked-int, which is false. Reversal: none. Owner: lane V (V1-c1, unit c1). Pin: none.

**V12 (CX-V D12).** e2-comm-ctor: the associativity axiom is sentence 186 of the fixture's account (`kore.txt:22`); 165 and 187 are the two `functional` axioms.

**NJ-0 beside d1 (CX-V §1, small).** d1's `consItemsK` keeps NJ-0's conditional, and the test stays on `gs`, every generator, open ones included: `(if gs.isEmpty then [] else [KoreAML.Cons.noJunkItem (n N) (gs.map (Gen.toK c))])`. The new case of `confinedAt_value` ("an open generator applied to values is the parameter graph's value or nothing") is edited by lane V in V2; Confined.lean is lane V's through V2 (K1).

**S6: shape 6, `requires A #Or B`.**
The sentence (`e3-ml-req-or/kore.txt:101`): `\equals{Bool,_}(\and{Bool}(\or{Bool}(A, B), _Gen0:Bool), true)`. For each element g of Bool, `(A ∪ B) ∩ {g} = {true}` holds exactly when g is `true` and `true ∈ A ∪ B`: the premise is `⌈A = true⌉ ∨ ⌈B = true⌉`, and the one fact about Bool it uses is that `true` is an element (`ΓDomains`). `_Gen0` is no reason to refuse. It is not `A orBool B` (where A is `true` and B has no value the premise holds and `orBool` has no value).
Fix: **the two-rule form**. Two rules of the rule's priority, left side, right side and `ensures`, one with `requires A`, one with `requires B` (reading note `requiresOrSplit`). `unheldVar?` is extended to the `requires`: a variable that only one of A, B holds and nothing else of the rule holds is dropped from the other rule, so that rule is read only where the variable's sort has an exhibited value (V3); otherwise the axiom is refused `unheldVariable`.
Reason, by cost and coverage. Both forms are sound and exact at values under `FnHyp` (CX-V). The two-rule form changes no cone declaration, lands in brief P now, and its rules are plain (`pre = .top`), so every consumer (`Exec`, `Det`, `Symbolic`, `NICells`) reads them with no change. `Cond.or` waits for R3, makes the rule non-plain, and is tied by a lemma about `_Gen0` instead of by entailment each way. `Cond.or` covers one case more: a variable in B only at a sort without an exhibited value.
Reversal: a fixture where that case is refused and a definition needs it; then `pre := or (equals Srt.bool A true) (equals Srt.bool B true)` after R3.
Known gap, no theory content: the two rules share the sentence's `UNIQUE_ID` (as `orSplit`'s do); the generator's certificate lookup by id takes the first (ticket in brief P, unit 3).
Owner: lane P. Pin: none.

## 4. The units still to build

### 4.1 Ownership of cone declarations

A brief owns the declarations its row lists, for its duration. Proofs, tests, the reader and fixtures are not listed: each brief edits its own.

| Lane | Declarations | Briefs that edit them |
|---|---|---|
| R | `ruleSorted` (final, landed), `rulesPlain`; the proofs of `sound_at`, `complete_at`, `exact_hyp`, `has_model_choice`, `consistent_of`, `famEx_values`, `famOpen_values`, `famEx_closed`; the rule cases of the model (`Model.StepM`, `StepE`, `stdI`); `Emit.rulePattern` | R1b, R1c, R1d, R2, R3 |
| F | `clauseSorted`, `clausesPlain`; the `Eval` block (`Eval`, `Fails`, `ReqFails`, `EvalTerm`, `EvalTerms`, and `Holds` from e3); `Clause.AppliesAt`, `Clause.DecidesAt`, `Clause.Decides`, `Coherent`, `CoherentAll`, `ClausesAgree`, `PrioDecided`, `FnSolves`; `lowerClauses`, `clauseEquation`, `competingEquation`, `exclusion`; `OvlSig`, `overloadsOK`, `ovlPairOK`, `norm`, `ovlOver`; in F3 only: `consItemsK`'s items for an overloading symbol, `distGuarded`, `funUncItem`, `injUncItem` | B1b, e3, F2 (none), F3 |
| V | `sortOf`, `dvOK`, `paramVal`, `paramsPlain`, `carriersOK`, `gens`, `genWf` (the open-generator conjunct only), `consSorts`, `collSortOK`, `consItemsK`, `ΓDomains`, `collNoJunk`, `collAxioms`, `builtinColls`, the hook tables, `silentTable`, `lawHooks`, `OpenTotal`, `valueSorts`; in CF-0 only: `Semantics.confinedAt`; from CF-0 through V2: the proofs of Confined.lean | V1-c1, V2 |
| P | none | P, P2 |
| no lane, no unit edits them | `Cond`, `Cond.kore`, `Cond.binder`, `Cond.conj`, `Cond.bound`, `Holds`'s constructors, `Step`, `NotApplies`, `applies`, `ruleRight`, `prioRuleK`, `Γcl`, `Γc`, `boolClosed`, `ΓFallback`, `Fn`, `Clause`, `Rule`, every pinned statement | STOP |

Within a lane the briefs run in order, so two briefs that run in parallel are always of different lanes, and the lane rows are disjoint at every time: `confinedAt` is edited in CF-0 only, and `consItemsK` passes from V to F only after V2 has ended.
Reassignments made by CN-4, each stated where decided: `confinedAt` to V (K1); `consItemsK`'s overload items and `distGuarded` to F in F3 (F1); `FnSolves`, `PrioDecided`, `norm`, `ovlOver` to F (F8, F1); `genWf`'s open-generator conjunct to V (d1).

### 4.2 The DAG

Waves are separated by an integration (`INT-A`, `INT-B`, `INT-C`: merge, packages regenerated and kernel-rebuilt, cones against `core-cone.txt`). Inside a wave the briefs of different lanes run in parallel; no two of them own one cone declaration (4.1).

```
INT ──┬─ R1b ─ R1c ─ R1d ───────────────┐
      ├─ V1-c1 [CF-0, NJ-0, c1] ────────┤
      ├─ B1b            (after CF-0)    ├─ INT-A ─┬─ R2 ─ R3 ──────────┐
      └─ P                              ┘         ├─ V2 ─ P2           ├─ INT-B ─ e3 ─ F2 ─ F3 ─ INT-C
                                                  └────────────────────┘
```

| Brief | Owner | Predecessors |
|---|---|---|
| R1b | lane R | INT |
| R1c | lane R | R1b |
| R1d | lane R | R1c; unit CF-0 of V1-c1 (the flip waits for it) |
| V1-c1 (CF-0, NJ-0, c1) | lane V | INT; CF-0 lands first, NJ-0 after it |
| B1b | lane F | INT; unit CF-0 of V1-c1 |
| P | lane P | INT |
| R2 | lane R | R1d, INT-A |
| R3 | lane R | R2; brief P (the B3 probe, the two-`?` fixture) |
| V2 | lane V | V1-c1, INT-A; brief P (fixtures e2-idem-ctor, e2-open-rule, the mixed-sort generator) |
| P2 | lane P | V2 (d2 after d1), V1-c1 (c2 after c1) |
| e3 | lane F | R3, B1b, INT-B; alone against lanes R and F |
| F2 | lane F | e3; brief P (fixtures for FR and EX) |
| F3 | lane F | F2, V2 (`consItemsK`, Value.lean); brief P (OV fixtures) |
| V3 | not built | decision V6 |

If V1-c1 was started before CN-4 with the c1 wiring first: CF-0 and then NJ-0 are committed as soon as the tree compiles at a c1 step; they edit `confinedAt`, `confinedAt_value`, `noJunkItem_mem`, `consItemsK`'s no-junk line and `satConsGoal`'s last branch, declarations the wiring does not edit (it may edit other declarations of the same files).
Files two parallel briefs both touch, to merge by hand at integration (not cone): ModelCarrier.lean (R2: the transition as a parameter; V2: the carrier under d1), Parse.lean (every lane adds at the end of its block), Confined.lean is not among them: it is lane V's from CF-0 through V2 (K1).

### 4.3 Briefs R1b, R1c, R1d (lane R)

Rules common to R1b and R1c:
- `rulesPlain` keeps `r.opens.isEmpty`; no pinned statement, no cone definition and no existing theorem's statement changes, except a hypothesis made weaker in place on a lemma that is neither pinned nor in the cone. Library, Pins, Axioms green at the brief's end. Confined.lean is read, not edited (K1).
- Every new lemma takes its facts about the rule as explicit hypotheses: `c.ruleSorted r` and the rule's conjunct of the flip text below (a non-cone `Bool`, lane's name). Never `rule_binds`, `sortedOK_rule` or `rulesPlain_rule`, which today give `opens = []`.
- Rule 0.7: one kernel-checked instance per arm a lemma covers (the shapes `ok1`, `ok2`, `ok4` of `test/RulesPlainArmC.lean`).
- If weakening hypotheses in place reaches a file that proves a pinned statement (Sound.lean, Obligations.lean, StepCompleteAt.lean), or more than a handful of lemmas, stop and report the count.
- Common stop rule: a lemma needs, of the rule, more than those two facts, or of the definition more than `FnHyp`'s conjuncts and the fields of `HypSoundCore` other than `rulesPlain`: stop with the rule shape. It is a candidate counterexample to the flip text, not a hypothesis to add.

**R1b: a successor's valuation can be taken at values (any model).**
1. For a term t sorted in the right side's context, a valuation ρ of elements, a value v with `elemOf v ∈ ⟦t⟧ρ`: for every `i ∈ ctorOccs c t`, ρ(i) is the element of a value of the sort of i. Stated over terms, no rule. (Injections: for `X:a` in `inj{a,N}(X)` against a normal form `inj{b,N}(w)`, by `cohItem`, `injItem`, `distItem`, `distLbItem`; if `distLbItem`'s overlap is not "the image of a listed lower bound", stop with that case.)
2. `stepDecided_of_fnHyp` for a rule with open variables: evaluations of the left side's conditions at `WellSortedAt r.vars r.leftVars`, of the right side at `WellSorted r.vars`.
3. For r with the two facts, a model of `Γc`, ρ with the left side, conditions and `⌈right⌉` at x and y's element in the right side: a σ of values with every premise of `StepBy` but `hprio`. Cases A (unit 1), B (`confined_value`; the hypothesis is `c.confined`, whatever its body), C (`CondDecided`: `Refuted` contradicts ρ; `Witnessed` supplies all of `condVars`, which `condApart` keeps out of the right side).
Stop rule, beside the common one: unit 1 fails for a generator `ctorOccs` passes through (report the symbol kind); unit 3's case C needs a condition variable outside the witness.

**R1c: competitors, and the value model.**
1. For a competitor r' with the competition conjunct and, where `needsWitness`, `CondDecided`: in a model of `Γc`, `NotApplies c r' x` gives `¬applies` at x's element; and `¬applies` gives `NotApplies` under `StepDecided`. `applies` binds `leftVars` only.
2. `sat_rule` and `applies_iff` for a rule with open variables: the axiom is closed over every variable of the rule, each occurrence read.
3. `consistent_of` over `Γc`: the value model satisfies `Γcl` by `boolClosed_model` where `readsConfined`.
Stop rule: the value model fails the axiom of a rule that the flip text and `ruleSorted` admit, or fails `boolClosed`: report the shape, change nothing.

**R1d: completeness, and the flip.** Starts when CF-0 is in its base.
1. `step_successor_at` split: a successor of x is a `Step` value by a rule with `opens = []`, or lies in `famOpen c r σ` for an `Unblocked` σ; `complete_at`'s family case from it.
2. `famOpen_values` for a rule whose open variables are confined, from R1b unit 3.
3. The flip, one commit. `rulesPlain` becomes:

```lean
def Semantics.rulesPlain (c : Semantics) : Bool := c.rules.all fun r =>
  r.exs.isEmpty && r.pre.isTop && r.post.isTop &&
  (let conf := fun i => (r.vars[i]?.map c.confined).getD false
   let rest := varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post
   let condApart := r.reqClosed && r.condVars.all fun j => !rest.contains j
   r.opens.all (fun i => (ctorOccs c r.rhs).contains i || conf i || (r.condVars.contains i && condApart)) &&
   (!r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed))
```

   Before the flip the lane lists every theorem of the library that exhibits a model of `Γ c` holding a Bool element that is no literal's (to read: `FaithfulColl`'s model; ModelJunkWitness and ModelJunkNonemptyWitness are not of that kind, their extra elements being of IOError). `Γ` is not edited, so each stands as a statement about `Γ`; under `Γc` such a model is lost for a definition that reads a confined sort, and the report says which theorems that concerns.
   `sound_at`, `complete_at`, `exact_hyp`, `has_model_choice`, `consistent_of`, `famOpen_values` re-proved from R1b, R1c and units 1, 2. The reader's `openRefusal`: for a variable failing the arms, `openRequires` (in a condition that also holds a bound variable; or in a closed condition that shares a variable with the right side, the `ensures` or `post`, the detail naming the shared variable) or `openRight` (R-D4). `test/RulesPlainArmC.lean` reads `c.rulesPlain`. `appOK`'s `binds` conjunct stays; the statements RC-3 listed (`sound_at_step`, `complete_at_step`, `star_entails`, `star_entails_nextN`, `Γc_core`, `run_exact` and their users) are restated with `plain` or re-proved.
Stop rule: `test/Pins.lean` needs any edit, or one of the six proofs needs a hypothesis its pinned statement does not have. Then units 1 and 2 land, `r.opens.isEmpty` stays, and the lane reports the proof and the rule shape. No partial flip.

| Fixture | Sentence | Expectation after the flip |
|---|---|---|
| e2-unbound | `kore.txt:94` | `wf true`; at `<k> a() </k>`, `Step` to `b(i)` for every Int i; `Γc ⊧ den x ⇒ •den b(i)`; `OutIs` with one `fam`; by `ExactC`, no value but a `b(i)` is a successor in any model |
| e2-rule | `kore.txt:170-186` | `wf true`, no `openRequires` (HOLE is in the `requires` of the `[cool]` and `[heat]` rules only, both below the `[owise]` rule, passing the competition conjunct by `reqClosed`); `Witnessed` with HOLE := `kseq(inj{Int,KItem}(0), dotk)` for `[cool]` and HOLE := `dotk` for `[heat]`; at `c(1)` the successor `b(1)` |
| e2-open-linked | `a() => b(X) requires X ==Int 2 *Int H` | refused `openRequires`, the detail naming H and the shared variable X |
| e2-open-linked-bool | `a() => b(#if B #then 1 #else 0 #fi) requires B ==Bool (2 *Int H ==Int 1)` | refused `openRequires`, naming H and B |
| e2-open-genless (new, from brief P; needs NJ-0 for its model) | CX-R's `E2-OPEN-GENLESS`: `a() => b() requires isMk(X:S)`, `S ::= mk(Empty) \| k()`, beside `a() => c() [owise]` | `c.confined S = false`; the rule is admitted by arm C, `needsWitness` true; `¬ r.Witnessed c` (the one value `k()` gives `false`); the account lists the rule's `CondDecided` as owed and open. `Step a() c()` holds at values; a soundness theorem is stated only under the owed fact as a hypothesis, named with its rule (R1d.gen-owed-wording, V1, 2026-11-16) |

### 4.4 Brief V1-c1 (lane V): CF-0, NJ-0, c1

1. **CF-0.** Decision K1, its text, its lemma `confined_has_value`, its test line. Validation: FaithOK, Confined and importers; Pins; regeneration with an empty diff; the cone row of `confinedAt` and the `Cond.bound` cone's one changed declaration reported.
2. **NJ-0.** `consItemsK`'s last line per sort becomes `(if gs.isEmpty then [] else [KoreAML.Cons.noJunkItem (n N) (gs.map (Gen.toK c))])`. `ModelCons.satConsGoal`'s last branch splits on `gs.isEmpty`; `noJunkItem_mem` takes `(hg : (c.gens N).isEmpty = false)`. `test/EmptySort.lean`: no item labelled `cons-nojunk SortEmpty`; `Loop`'s item is the translation of sentence 131 of `emptysort.kompile.kore`. `ΓCons`'s doc line "the sort holds nothing but what its generators build" gains "where it has a generator". Stop rule (N1's reversal): a proof of a `Γ ⊧ …` statement used the item at an empty generator list other than `confinedAt_value`; report it, change nothing.
3. **c1.** The wiring of the landed `rangeMapHooks` (the plan is in the V1 report, which CN-4 did not read; section 7). What CN-4 fixes about it: `sortOf` gains the `.rangeMap` arm with `rangesOK`; `collAxioms … | .rangeMap => []` stays (`Γ` says nothing of range-map symbols at elements that are no value's, which is right while `rangeMapPattern` is refused); `(Range, KItem)` is in `subsorts` (`rmKeys` builds `inj{Range, KItem}` members); `patternHooks` and `collPatternHooks` gain **no** range-map symbol (V6); `valueSorts`'s seed gains the carrier sorts (V10); `rangeMapPattern`'s docstring is V6's reason. Lemma: `sortOf`'s `keysSorted` order and `rangesOK`'s order of lower bounds agree.

Fixture `e6-rangemap`, expectations from `rangeMapHooks` and the sentences (`kore.txt:70`, `:72`, `:74` the three laws, which hold at values under a concatenation that merges and is defined where key sets are disjoint): sizes 2, 1, 3, 2; `find_range(merged, 4) = [0,5)`; `m[1] = a`; `m[3] orDefault c = c`; `2 in_keys` true, `3 in_keys` false; the difference is `[0,3) r|-> a, [5,10) r|-> a`; an overlapping concatenation has no value (`¬⌈…⌉`); `M[9]` is undetermined over the interpretations (silent, RM-3). The overlap of two entries of one value, `([0,3) r|-> a) ([2,5) r|-> a)`, has no value in the landed table; whether domains.md:498-500 says otherwise is open (section 7) and the fixture does not assert it either way.

### 4.5 Brief B1b (lane F)

Starts when CF-0 and R1's lemmas (`boolClosed_model`, `boolValues`, `confined_value`) are in its base.

1. **B1b.** Clauses with a variable their patterns do not bind. **COLD-REVIEW** (with F8): CN-3 gave this unit prose only; the two bodies below are CN-4's, in cone declarations under `coreOK`. What is new in them: `binds` over every occurrence (each variable occurs somewhere in the clause, as `ruleSorted` asks of a rule, reading U1-2), and F-1 as the last conjunct of `clausesPlain`.

```lean
def clauseSorted (f : Fn) (rhsHeads : List CtorSig) (cl : Clause) : Bool :=
  sortsOfTerms c.patCtxAll cl.vars cl.pats == some f.args &&
  binds cl.vars.length (varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
    (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post) &&
  reqOK (c.rhsCtx rhsHeads) cl.vars cl.req &&
  sortOfTerm (c.rhsCtx rhsHeads) cl.vars cl.rhs == some f.result &&
  reqOK (c.rhsCtx rhsHeads) cl.vars cl.ens &&
  (Cond.bound c cl.vars.length cl.pre && Cond.bound c cl.vars.length cl.post)

/-- Clauses bind no variable by `\exists` and have no predicate; and a clause's open condition
variables are of confined sorts, or its conditions are closed (`OpenDecided`). -/
def Semantics.clausesPlain (c : Semantics) : Bool := c.fns.all fun f => f.clauses.all fun cl =>
  cl.exs.isEmpty && cl.pre.isTop && cl.post.isTop &&
  (!cl.reqOpen || cl.reqClosed ||
    cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false)
```

   (`clauseSortedT` the same.) An open variable of the right side or the `ensures` is admitted at any sort: each instance is an equation of the same `f(x̄)`, so an instance at an element that is no value's agrees with the values' or leaves no model; `MatchIndependent` asks that the result does not depend on it. No `condApart` for clauses (F1-DECISION §7.3). No "largest priority" case (F-1).
   `readsConfined` is then true for such a definition, so `Γc c = Γ c ∪ {boolClosed c}` where `litSort Srt.bool`: `Γc_core` and `readsConfined_of_core` go (their readers: twelve `rw` in Sound.lean, ModelFunctional.lean:371; no pinned statement reads them); the model conjunct is re-proved with `boolClosed_model`; `Γc_plain` (pinned) stays, by `readsConfined_of_plain`.
2. **e2-cool-eq** and the genless clause.
3. **The §7.3 account check**: for a clause with `needsWitness`, the account lists its `CondDecided` among the owed facts, named with the clause, open until `Witnessed` or `Refuted` is shown. If the account does not print it, that is a reader gap to fix here, not a reason to refuse the clause.

| Fixture | Sentence | Expectation |
|---|---|---|
| e2-cool-eq | `kore.txt:342`, `f(X) => X requires isKResult(HOLE:K)` | `wf true`; `needsWitness` true; `Witnessed` with HOLE := `kseq(inj{Int,KItem}(0), dotk)`; `Eval f [int 3] (some (int 3))`; the second sentence stays `inert simplification` |
| the title clause of F1-DECISION §7.3 | `f() => 0 requires 1 ==Int 2 *Int H` | admitted; `¬ cl.Witnessed c`; `CondDecided` listed as owed and open |
| e2-clause-genless (new, from brief P) | CX-F 5's text: `f() => 1 requires isC(H:S)`, `f() => 0 [owise]`, `S ::= "a" \| c(Empty)` | `c.confined S = false`; the clause is admitted by the closed case, `needsWitness` true, `¬ Witnessed`; `CondDecided` owed and open; no theorem stated |

Stop rule: any pin has to change; or `eval_plain`, `evalTerm_plain`, `fails_plain`, `fnItems_plain` cannot be proved at their types.

### 4.6 Brief P (lane P, reader and fixtures; no cone)

1. **The narrowed `unheldVariable` and shape 6.** Decisions V3 and S6, with NONEMPTY §3 Q4's table for shapes 1 to 5:
   - `C[∃Y:S. φ] => R`, Y not in φ, S with an exhibited value: the rule `C[φ] => R` (`existsAsVariable`, the binder dropped);
   - `C[d₁ #Or d₂] => R` with a variable x:S that one disjunct does not hold and nothing else of the rule holds, S with an exhibited value: `orSplit`, x absent from that disjunct's rule; `a(_) #Or b(_)` is this twice (each sort needs a value; if only one has, the axiom is refused whole);
   - the same at a sort without an exhibited value: `unheldVariable`. The reason, after NJ-0: `Γ` entails neither an element of the sort nor its emptiness, so the sentence may be vacuous where the read rule would step;
   - a variable some disjunct does not hold and the right side, `requires` or `ensures` uses: an open variable of that disjunct's rule, decided by `rulesPlain` after R1d (`unboundVariable` before it);
   - shape 6: S6.
   The tie lemma `inhabited_of_value` (NONEMPTY §6 A3) is stated with the tie lemmas; `orSplit` is exact with overlapping disjuncts (two rules' sentences are together the one sentence; a successor reached twice is one successor).
2. **Kompile probes.** Each fixture is the K text, `kore.txt` or `kompile.txt`, and the account; a text kompile rejects makes its row R-b. No reader arm is built here for a shape another brief builds.

| Fixture | Text | For |
|---|---|---|
| e3-rule-lhs-fun | `rule <k> c(f(X:Int)) => d(X) ... </k>`, f total with `f(1) = f(2)` | R-D2 (R3's B3 unit exists only if accepted) |
| e3-vars-two | a rule with `?Y` and `?Z` on the right side | R2 (the order of `exs` is the text's nesting) |
| e3-vars-bool | `rule <k> c() => d(?Z:Bool) </k>` | R2 |
| e3-vars-map | `<m> K \|-> ?V:Int </m>` on a right side | R-D4 (records the sentence; refused `openRight`) |
| e2-open-genless, e2-clause-genless | CX-R D1's and CX-F 5's texts | R1d, B1b |
| e3-ml-eq-rhs-or-total | `h(X) => f(X) #Or g(X)`, h `total`; and the same without `total` | F6 |
| e3-eq-exists-bool | `syntax Bool ::= f(Bool) [function, total]`, `rule f(X) => ?B ensures ?B ==Bool notBool X`; the Int form `?Z *Int 2 ==Int X` | F4 |
| e3-setvar-linear, e3-setvar-nonlinear | `rule w(@S) => @S`; `rule f(@S, @S) => r`, outside `[simplification]` | F7 |
| e5-ovl-fun | `syntax Exp ::= Exp "+" Exp [overload(plus)]`, `syntax Int ::= Int "+" Int [function, overload(plus)]`, `syntax Exp ::= Int`, `rule I1 + I2 => I1 +Int I2` | F1 |
| e5-ovl-fun-lhs | `ovlfun.k` with `rule <k> run(cap(G:Gas)) => done(G) </k>` | F2 |
| e5-ovl-fun-keep | CX-F 3's text (`cap(Gas)` overloaded by `cap(N) [function, total]`, `rule cap(z) => inf`) | F3 |
| e2-idem-ctor | `syntax Exp ::= Exp "\|" Exp [idem]` on a production that is no collection concatenation | V7 (which of its three cases the text is) |
| e2-open-mixed | `syntax A ::= "a"`, `syntax B ::= A "&" A [comm, symbol(and)]` | V3, V9 (whether kompile writes an open generator across sorts) |
| e2-unit-ctor | `[unit]` on such a production | section 5, `openLaw (unit)` |
| ml-value | NONEMPTY's `mlempty` rules with `Empty` replaced by a sort with a constructor; `a(_) #Or b(_)` over Int | unit 1 |

3. **Housekeeping.** `test/constructs/rows.toml`: the stale rows named in TICKETS (KREFLECTION.configuration, `#Or` reader_does_it, E7 guardOrs, the ML rows quoting `patternConnective`, E3 rows now read), and the rows of section 5. The generator's certificate lookup by `UNIQUE_ID` takes the first of several rules of one sentence (`orSplit`, `requiresOrSplit`): look up by id and position.

Expectations for unit 1: `mlempty` keeps `refused unheldVariable` (2 axioms); `ml-value`: `existsAsVariable` and `orSplit`, `c(a)` and `d` each stepping to `b`; `e3-ml-req-or` (`kore.txt:101`): two rules, and where A is `true` and B has no value the rule with `requires A` steps.

### 4.7 Brief V2 (lane V): d1, d3, ID

The sentence the brief carries, HOOK-READING §4 as corrected by V1 (it replaces that section's sentence):

> **A package whose text has an open generator states each of its theorems for every `H`, with `OpenLaws (d.sem.withHooks H)` and `OpenTotal (d.sem.withHooks H)` as named obligations among its hypotheses; it never discharges either by fixing `H`, and states no theorem only at one interpretation. Beside each theorem it states the instance at `lawHooks d.sem H` for every `H`, with the obligations discharged by `openLaws_lawHooks` and `openTotal_lawHooks`, and proves `libAdmitted_lawHooks` (HOOK-READING §1), so that `lawHooks d.sem HookParams.lib` is exhibited as satisfying the laws, the generators' `functional` sentences and the library's sentences together. `lawHooks` is the witness that the class is inhabited, not the meaning of the generator: a fixture expectation that holds only at the free interpretation is written as holding at `lawHooks`, and one the text states is written for every `H` with `OpenLaws` and `OpenTotal`. If a theorem cannot be proved for every such `H`, stop and report; do not restate it at `lawHooks`.**

1. **d1: open generators.** The Lean of `sortOf`'s open-generator arm (`keepsRaw`), `paramVal` at a `raw` parameter, `gens` and `consItemsK` is `designs/CN-2-term-level-constructs.md` lines 276-336, which CN-4 did not read (section 7); the brief reads that block and nothing else of CN-2, with these amendments, which hold over it:
   - `OpenTotal` and its three lemmas (V1); `totalParams` leaves `raw` parameters out;
   - `sortOf_withHooks`, `sortsOf_withHooks`, `sortOf_withHooks_rawFree` and the readers (V2);
   - `paramsPlain` is V8's body;
   - `consItemsK` keeps NJ-0's conditional, on every generator; it writes the associativity axiom of each `raw`, `assoc` parameter and the idempotence axiom of each `raw`, `idem` one, no functionality, injectivity or distinctness item for an open generator, and the no-junk item over all generators;
   - `genWf` asks an open generator's result to be a constructor sort;
   - `patCtxAll` gains no `raw` parameter (the decided form of `openGeneratorPattern`);
   - Confined.lean: `confinedAt_value`'s case for an open generator (an open generator applied to values is the parameter graph's value or nothing).
2. **d3.** `lawHooks (c : Semantics) (H : HookParams) : HookParams`: H everywhere except at the `raw` parameters; there, the right-nested application of the flattened arguments where `assoc`, equal adjacent arguments merged where `idem`. Statements:

```lean
theorem openLaws_lawHooks (c : Semantics) (h : c.coreOK = true)
    (hl : ∀ k ∈ c.params, (k.raw && k.assoc && k.idem) = false) (H : HookParams) :
    OpenLaws (c.withHooks (lawHooks c H))
theorem libAdmitted_lawHooks (c : Semantics) (h : c.coreOK = true) (H : HookParams)
    (ha : (c.withHooks H).libAdmitted) : (c.withHooks (lawHooks c H)).libAdmitted
example (c : Semantics) (h : c.coreOK = true) (hf : c.floatShapeOK = true)
    (hl : ∀ k ∈ c.params, (k.raw && k.assoc && k.idem) = false) :
    OpenLaws (c.withHooks (lawHooks c HookParams.lib)) ∧ OpenTotal (c.withHooks (lawHooks c HookParams.lib)) ∧
    (c.withHooks (lawHooks c HookParams.lib)).libAdmitted
```

   `libAdmitted_lawHooks` holds because no total silent symbol of `totalSilentKeys` takes an argument of a sort that holds a raw application; the lane states it with that reason, and stops with the sentence if a library sentence reads a `raw` parameter.
   The laws' tie: the axiom of `Γ` is the translated sentence (equal).
   To run at integration: `∀ k ∈ koreSem.params, k.raw = false` by `decide`, so that the KORE in K row's `HookParams.none` is unaffected.
3. **ID.** Decision V7.

| Fixture | Expectation |
|---|---|
| e2-comm-ctor | sentence 186 (`kore.txt:22`, associativity) is an axiom of `Γ`; sentences 165 and 187 (`functional`) are stated at values under `OpenTotal`; for every H with `OpenLaws` and `OpenTotal` the package's `Consistent`, sound, complete and exact statements hold; at `lawHooks` both obligations are discharged; at `HookParams.none` `OpenTotal` holds and `OpenLaws` fails (`or(or(x,x),x)` and `or(x,or(x,x))` are distinct raw values) |
| e2-open-rule (text in CN-2 §5; `and` has no law, so `OpenLaws` is true at every H) | for every H with `OpenTotal`, `go` has one successor; `same(x & y, y & x)` is `false` at `HookParams.none` (two distinct raw values) and `true` at the H with `app and [y, x] = some (.ctor and [x, y])`; at an H that answers `and [x, y]` ill-sorted, `OpenTotal` fails and nothing is stated |
| e2-idem-ctor | V7's three lines, if the text is case 2; `lawAxiom` if case 3 |

V2 checks its expectations on hand-built semantics (the reader refuses an open generator until d2); the same expectations on the kompiled fixtures are P2's.
Stop rules: HOOK-READING's; a `…_withHooks` lemma whose restated form a pinned statement's proof cannot use; `consistent_of` unprovable at its pinned type under d1.

### 4.8 Briefs R2 and R3 (lane R)

**R2: existential variables.**
1. The value model with its transition a parameter (`Model.stdI`, `StepM`, `StepE`); `satRulesGoal` from `hall` and `hsome`, `satStepGoal` from `hsub`; `has_model_choice` and `famEx_values` proved in full at their pinned types; `consistent_of` as the instance T := `StepM`.
2. `exs` admitted: `rulesPlain` loses `r.exs.isEmpty` (an existential variable passes by arm A or B only; it is never in `condVars`, by `ruleSorted`). The reader reads `\rewrites(lhs, \exists(…, right))`, `exs` in the text's order of nesting; `existentialRhs` goes for the admitted shapes. `Emit.rulePattern`'s right side becomes `ruleRight`'s text under the presentation's names: `(r.exs.filterMap (vs[·]?)).foldr (fun v p => .exist C v.kore p) (\and(rhs, ens))`; with `exs = []` every package's emitted text is unchanged.
3. Fixtures and the counter-example for the old soundness text.

| Fixture | Expectation |
|---|---|
| e3-vars (`kore.txt:185-191`: `\rewrites(\and(lhs, \top), \exists(Var'Ques'Z:SortInt, \and(rhs, \top)))`) | `stage refusals: 0`; at `c(1, 2)`: `Step` to `d(i)` for every Int i; `Γc ⊧ den x ⇒ •famEx`; `Γc ⊧ den d(i) ⇒ famEx` |
| e3-vars-bool (`c() => d(?Z:Bool)`) | `Step` to `d(true)` and `d(false)`; `has_model_choice` with `T x y := Step c x y ∧ y ≠ d(false)` gives a model in which `den x ⇒ •den d(false)` fails, so no single instance is entailed; `famOpen_values` with `ys = [d(true), d(false)]` |
| `c() => d(?Z:Int) ensures ?Z *Int 2 ==Int 1` (hand-built or fixture) | admitted (arm A); no `Step`; the value model satisfies the axiom (`⌈∃Z. right⌉` is false) |
| `c() => c() ensures ?Z ==Int 0` | refused `openRight` (Z:Int under no constructor) |
| e3-vars-two | `exs` in the text's order; the emitted sentence equals the text's |

**R3: predicates of a rule.**
1. `pre`, `post` admitted: `rulesPlain` loses `r.pre.isTop && r.post.isTop` (final body: the `let` block alone under `c.rules.all`). The `Holds` lemma: for a condition p with `condOK` and `Cond.bound`, a value substitution σ well sorted on p's free variables, in every model of `Γc`: the theory entails `Cond.kore p` at σ where `Holds … p true` and its negation where `Holds … p false`. Its hypotheses, all of them: `coreOK`; the clause hypothesis `hc` of `sound_at`; `readsConfined`; the predicate sort has a value (for the "false" half; at an empty sort both halves hold). Written by structural recursion on p with the soundness of `EvalTerm` as a hypothesis, so that e3 only supplies that hypothesis mutually. `famEx_closed` extended to a `post` that `Cond.bound` admits, statement unchanged. Consumers: `Det.StepBy`, `Symbolic.Fires`, `ModelCarrier.StepM` gain `Holds … pre true` and `Holds … post true` (each is tied to `Step` by an iff, so a missing premise fails in the kernel); `appOK`, `ensOK` as R-D3; `execReady` states the plain shape of rules itself once `rulesPlain` no longer does.
2. Reader arms. A connective in a term position of the right side (`\or`, `\top`, `\not`, `\and`) is read as `?Z` there with `post := mem s Z φ` (`C[φ] ≡ ∃Z. C[Z] ∧ Z ∈ φ` in every interpretation; `mem`, not `equals`). A complement on the left side is read as a variable with a `pre`. Binders: R-D6's guard and tie.
3. B3, only if `e3-rule-lhs-fun` was accepted by kompile (R-D2): `c(f(X))` read as `c(V)` with `pre := mem s V f(X)`.

| Fixture | Sentence | Expectation |
|---|---|---|
| e7-guardors | `kore.txt:39-45`: `Lblc(\or{Exp}(Lbla(), Lblb()))` on the left, `Lbla()` on the right | read as `orSplit` (landed); `c(a)` and `c(b)` have the successor `a`; `c(c(a))` none |
| e3-ml-rule-lhs-not | `kore.txt:51-56`: `Lblc(\not{Exp}(\and{Exp}(Lbla(), Var'Unds'Gen5:SortExp)))` on the left, `Var'Unds'Gen5` on the right, free | left side `c(Z)`, `pre := not (and (mem Z a) (mem Z G))`, right side G. `Step c(z) g ⟺ ¬(z = a ∧ g = a)` for all values z, g of Exp. Admitted because it is the only rule (G passes by arm A); beside a rule of larger priority it prints `openRequires Exp` |
| e3-ml-rule-rhs-or | `kore.txt:63-68`: `…inj{Exp,KItem}(\or{Exp}(a, b))…` | `?Z:Exp` with `post := or (mem Z a) (mem Z b)`; `famEx` is `C[a] ∨ C[b]`; `Step` to both; by `has_model_choice` (`T` := `Step` less the b instance, and symmetrically) neither `den go ⇒ •den a` nor `den go ⇒ •den b` is entailed |
| e3-rule-lhs-fun (if accepted) | | `c(v)` with `f(1) = f(2) = v` has the `Step` successors `d(1)` and `d(2)`, each entailed alone (`exs = []`); where `f(X)` has no value the rule does not apply; beside a larger rule: `openRequires Int`; with X in f's argument only (`=> d(V)`): refused |

Stop rules: a consumer theorem needs a statement change that is pinned; `famEx_closed` or the `Holds` lemma needs a hypothesis beyond those listed.

### 4.9 Brief e3 (lane F, alone against lanes R and F)

Three units: (1) `Holds` joins the `Eval` block with its constructors unchanged (`PatVal`, `PatVals` stay outside the block: `Holds.exSome`'s `hr` holds `PatVal` under `↔`), and every mutual induction gains its cases; (2) `Clause.pre` in evaluation (`Eval.clause`, `Eval.ensFails`, `ReqFails.pre`, `Clause.AppliesAt`, `Clause.DecidesAt`, `PrioDecided`); (3) `Clause.pre` in the sentences (`clauseEquation`, `competingEquation`, `exclusion`), `clauseSorted`, `clausesPlain`. `Clause.post` and `Clause.exs` are not admitted (F8, F4).
**Gate.** A clause `pre` is produced by F6 and F4 only. If brief P's probes `e3-ml-eq-rhs-or-total` and `e3-eq-exists-bool` are both rejected by kompile, e3 and F2 are not built: `Holds` stays outside the block, `clausesPlain` keeps `cl.pre.isTop`, and F3 follows B1b and V2 directly.

```lean
-- Evaluation.lean, in the block (to run): the three edits
    | clause … (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
        (hpre : Holds c cl.vars.length σ cl.pre true)
        (hprio : …) (hrhs : …) (hens : …) : Eval c f vs r
    | ensFails … (hreq : …) (hpre : Holds c cl.vars.length σ cl.pre true) (hprio : …)
        (ht : …) (he : …) (hw : …) : Eval c f vs none
  inductive ReqFails (c : Semantics) : Subst → Clause → Prop where
    | intro … -- as landed
    | pre {σ : Subst} {cl : Clause} (h : Holds c cl.vars.length σ cl.pre false) : ReqFails c σ cl

-- EvalFunctional.lean
def Clause.AppliesAt (c : Semantics) (cl : Clause) (σ : Subst) (vs : List GroundTerm) : Prop :=
  c.WellSorted cl.vars σ ∧ PatVals c σ cl.pats vs ∧
    (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c cl.vars.length σ cl.pre true

def Clause.DecidesAt (c : Semantics) (fn : Fn) (cl : Clause) (σ : Subst) (vs : List GroundTerm) : Prop :=
  cl.AppliesAt c σ vs ∧
    ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
      ∀ σ', c.WellSortedAt cl'.vars cl'.leftVars σ' → PatVals c σ' cl'.pats vs →
        ¬ ((∀ t, cl'.req = some t → EvalTerm c σ' t (some (bool true))) ∧
           Holds c cl'.vars.length σ' cl'.pre true)

-- FnSolves.lean
def PrioDecided (c : Semantics) : Prop :=
  ∀ fn ∈ c.fns, ∀ vs cl σ, cl ∈ fn.clauses → cl.AppliesAt c σ vs →
    ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
      ∀ σ', c.WellSortedAt cl'.vars cl'.leftVars σ' → PatVals c σ' cl'.pats vs →
        (∀ t, cl'.req = some t → ∃ r, EvalTerm c σ' t r) ∧ ∃ b, Holds c cl'.vars.length σ' cl'.pre b
```

`Fails`, `Clause.Decides`, `Coherent`, `CoherentAll`, `ClausesAgree`, `MatchIndependent`, `FnSolves`, `FnDet`, `Eval.rest`, `ΓFallback` keep their texts (they read the edited ones by name).
The premise of a clause's sentences gains the predicate, written so that a clause with `pre = .top` has the landed text:

```lean
-- Emit.lean / Faithful.lean (to run). `prem` is the landed `premise …` application of each.
/-- A clause's premise with its predicate: the landed premise where the predicate is `\top`. -/
def withPre (c : Semantics) (vs : List KoreAML.Var) (cl : Clause) (prem : Kore.Pattern) : Kore.Pattern :=
  if cl.pre.isTop then prem else .and R [prem, Cond.kore c vs R cl.pre]
```

- `clauseEquation`: `eqnSentence c f (withPre c vs cl (premise …)) (Term.kore c vs cl.rhs) (reqPat …)`;
- `competingEquation`: `competingPremise`'s last conjunct `premise args req pats` becomes `withPre c vs cl (premise args req pats)` (lane's to spell: inline the conjunction or give `competingPremise` the pattern);
- `exclusion`: `existsAll R (bound.map KoreAML.Var.kore) (withPre c ren cl (premise …))`, `ren` the presentation's names (`bound` already ranges over `cl.leftVars`, which holds `pre`'s variables through `condVars`).

`clauseSorted` gains `&& condOK c cl.vars cl.pre`. `clausesPlain` becomes (final):

```lean
def Semantics.clausesPlain (c : Semantics) : Bool := c.fns.all fun f => f.clauses.all fun cl =>
  cl.exs.isEmpty && cl.post.isTop &&
  (!cl.reqOpen || cl.reqClosed ||
    cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false)
```

Outside the cone: `execReady` gains "every clause has `pre = .top`" (the executable evaluation reads `req` only), as `asideFree` was added.
What each text states, for the reviewer: a clause applies at σ where its patterns match, its `requires` is `true` and its `pre` is true; it fails at `vs` where at every match one of the two is not so (`ReqFails.intro`, `ReqFails.pre`); `Γ`'s sentence for it has the premise `⌈req = true⌉ ∧ X̄ ∈ p̄ ∧ pre`, and a larger clause's premise negates `∃(leftVars). (⌈req = true⌉ ∧ X̄ ∈ p̄ ∧ pre)`. `Eval` and `Γ` agree at values by R3's `Holds` lemma, whose `EvalTerm` hypothesis the block now supplies.
Expectation (kernel test, hand-built): `u(X:Int) => X ensures X >Int 0` (so `u(0)` has no value, by `ensFails`, at every interpretation) and `g(X:Int)` with the clauses `pre := ceil Srt.int (u(X))`, `rhs := 1` (priority 50) and `rhs := 0` (200): `Eval g [int 0] (some (int 0))` and no other result; `Eval g [int 2] (some (int 1))` and no other; `Γ`'s sentence for the second clause carries `¬ ∃X'. (X ∈ X' ∧ ⌈u(X')⌉)`.
Stop rules: positivity fails; a `…_plain` lemma is not provable at its pinned type; `fnDet_of_coherent`, `fnSolves_of_total` or the model's uses of `eval_of_decides` need more than the texts above.

### 4.10 Briefs F2 and F3 (lane F)

**F2: `#Or` and `?B:Bool` on an equation's right side (reader only).**
1. FR: decision F6. 2. EX: decision F4 (`existsAsCases`; the reader checks `f.total` and, on the built definition, `litSort Srt.bool`). 3. The tie lemmas: for a total f, the n+1 clause equations follow from the translated sentence and f's functional sentence, and entail the sentence; for F4, with `boolClosed`.
Fixtures and expectations: F6's and F4's, on `e3-ml-eq-rhs-or-total` and `e3-eq-exists-bool`. If kompile rejected a text, its row is R-b and its unit is not built.
Stop rule: a tie lemma needs a premise other than those named.

**F3: OV (decisions F1, F2, F3).**
1. `funUncItem`, `injUncItem`; `consItemsK` and `distGuarded` for a function-overloaded symbol; the model's cases (a covered application of such a symbol denotes `inj (g …)`; uncovered raw applications are values, injective and apart as today).
2. `OvlSig.over` may name a function of `c.fns`; `overloadsOK` admits it where the function's argument and result sorts are at most the symbol's (`ovlPairOK`) and adds `ovlPatsOK` (F2; `symOccs`, `condPats`, `fnOvlSyms` are the lane's helpers: the applied symbols of a term, the `exMatch` patterns of a condition, the function-overloaded symbols); `EvalTerm`'s new case and `EvalTerm.ovl`'s premise; `norm`, `ovlOver`. `eval_plain` re-proved (`plain` holds no function overload).
3. The reader (the `symbol-overload` axiom of a function-overloaded symbol is read; `overloadForm` goes for it; the note `overloadFunction`), fixtures.

| Fixture | Expectation, from the overload equation and the function's equations |
|---|---|
| e5-ovl-fun | `coreOK`, `FnHyp`, `Consistent`; `EvalTerm` of the Exp-level application at `inj(1), inj(2)` is `inj(3)`; the account's note says sentences "functional" and "no confusion" of `plusExp` are read at uncovered arguments, and that the text has no model (`1 + 2` and `2 + 1` are both `inj(3)`, against its no-confusion sentence) |
| `ovlfun` (landed text: N has the one value `z`, `capN(z) = z`) | `capGas(inj z)` evaluates to `inj z`; the text has a model; the note is printed without the "no model" sentence being claimed (the reader does not decide injectivity) |
| e5-ovl-fun-lhs | refused `functionInPattern`; `c.ovlPatsOK = false` on the hand-built semantics of the same rule |
| e5-ovl-fun-keep | read; `capGas(inj z)` evaluates to `inf`; `Consistent`; the note |

Stop rules: a proof needs injectivity or totality of a function-overloaded symbol at a covered argument (F1's reversal: report it); `ovlCoherent` admits two function overloads covering one argument list.

### 4.11 Brief P2 (lane P, reader; no cone)

1. **c2** (after c1): the reader rows of RANGEMAP. What the e6 account shows it has to move: 20 sentences `refused builtinText`, the three law sentences of `_RangeMap_` listed `lawAxiom` (to be classed as the laws of a collection's concatenation, stated at values: associativity and the two unit laws hold at values under `rmConcat`), four unaccounted sentences of `isRange` and `isRangeMap`. A range-map symbol binding a variable in a left side prints `rangeMapPattern`. (CN-3 gave c2 no text beyond its name, and CN-2's was not read: section 7.)
2. **d2** (after d1): the reader rows of open generators, with V9's rows and V7's order of classification (set concatenation, open generator, anything else). The exhibited-value test stays "applies no open generator" (V3).
3. The rows of section 5 in `rows.toml`; fixtures `e2-open-mixed`, `e2-unit-ctor` read or refused as section 5 says.

## 5. What stays refused

Each row: the `RefusalReason` the reader prints, the shape, where it applies, the decided condition under `coreOK` that keeps a hand-built semantics of the shape out of the theorems (rule 0.3; "none needed" where the semantics cannot hold the shape or holding it is sound), and the kind with its reason. R-a: on first principles, the text gives the construct no meaning a `Step` or `Eval` on values can be sound and exact for. R-b: kompile rejects the text. R-c: not supported at this freeze, naming the cone declarations that would change.

| `RefusalReason` | Shape | Applies where | Decided condition | Kind and reason |
|---|---|---|---|---|
| `openExtent s` | a quantifier or a `\floor` of a term over the sort s, in a condition | s unconfined (the reader, sentence by sentence: every sort but Bool) | `Cond.bound` in `ruleSorted`, `clauseSorted` | R-a: its truth at given values differs between models of the text (2.3) |
| `openRequires s` | a variable no left side binds, of sort s, in a condition that also holds a bound variable; or in a closed condition of a rule one of whose variables the right side, the `ensures` or `post` holds | s unconfined; for a rule: the variable not held by the right side under constructors, or the rule competes with a larger one; for a clause: always | `rulesPlain`, `clausesPlain` | R-a: an element that is no value's may satisfy the condition; with a shared variable it gives a successor that is a value's and that no value gives (`a() => b(X) requires X ==Int 2 *Int H`) |
| `openRight s` | a variable no left side binds, or an existential one, of sort s, that the right side, `ensures` or `post` holds under no constructor and no condition holds | s unconfined; (i) under a function or hooked symbol; (ii) under a collection's symbols | `rulesPlain` | (i) R-a: `c() => d(f(?Z:Int))` has a value successor through an element that is no value's. (ii) R-c: `ctorOccs`, `rulesPlain` (an arm "held under collection symbols", unproved) |
| `existentialEquation s` | `\exists` on an equation's right side, other than one variable of Bool on a `total` function in a definition where Bool holds only literals (read, F4) | (i) s unconfined; (ii) s confined and not that shape, or the function not total | `clausesPlain` (`cl.exs.isEmpty`) | (i) R-a: the function's value ranges over elements the text does not name. (ii) R-c: `Clause`, `clauseEquation`, `Eval.clause`, `Coherent`, `FnSolves` |
| `manyValuedRightSide` | on an equation's right side: `\or` where the function is not `total`, or more than 8 alternatives; `\top`; `\not`; an `\exists` that is not `existentialEquation`'s | always | none needed: `Term` has no connective | `\or`, not total: R-c (`Clause`, `clauseEquation`, `Eval.clause`): the sentence gives the function every element of each side, more than one where they differ, which no clause states and the text does not exclude. More than 8: R-c (cost). `\top`, `\not`: R-a: the value is a sort's extent or a complement in it |
| `setVariable` | a set variable outside a `[simplification]` axiom | always | none needed: `Term` has no set variable | linear: R-a if the fixture `e3-setvar-linear` shows the `\in` form (the sentence then states the function's value for every set holding the argument, which has no model at a sort with two elements); if it shows the direct form, the row goes and the variable is read as an element variable (F7's reversal). Non-linear: R-c (`Fn`, `Eval.rest`, `ΓFallback`: nothing can state "no result and no premise" off the diagonal) |
| `unheldVariable` | a rewrite axiom with a variable that a rule read from it would not hold: bound by `\exists` in the left side and absent from its body; or held by one disjunct of the left side (or of a `requires A #Or B`) and by nothing else | the variable's sort has no exhibited value that applies no open generator | none needed: the read rule is not built | R-a: the sentence holds for every element of the sort, so where the sort has none it states nothing while the rule without the variable would step; `Γ` entails neither an element of such a sort nor its emptiness |
| `functionInPattern` | a rule's left side, a clause's pattern or an `exMatch` pattern that applies (i) a function, parameter or hooked symbol that is no collection pattern symbol; (ii) an overloading symbol with a function overload | always | (i) `patCtxAll` in `ruleSorted`, `clauseSorted`, `condOK`; (ii) `overloadsOK` (`ovlPatsOK`) | (i) in a rewrite rule: R-b if the probe `e3-rule-lhs-fun` is rejected, else read as the cut (R-D2). (ii) R-c: matching it inverts a function; the cut would state it (`rulesPlain`'s arms then decide it) |
| `overloadAxiom` | a `symbol-overload` axiom whose larger symbol is itself a function | always | none needed: `isOvl` is false of a function | R-c (`Eval`): the equation is one more equation of that function, outside its clauses |
| `openGenerator` | an open generator whose result sort is no constructor sort (Int, a collection sort); before d2: every open generator | always | `genWf` | R-a: an open generator is a generator of its sort, listed in the sort's no-junk sentence; a sort that is no constructor sort has no such sentence in the theory |
| `openGeneratorPattern s` | an open generator binding a variable in a left side | (i) its sort is recursive or reaches an unconfined sort; (ii) its sort is confined | `patCtxAll` holds no `raw` parameter | (i) R-a: matching needs which elements the sort has and which arguments the uninterpreted symbol sends to the value. (ii) R-c (`PatVal`, `patCtxAll`): the preimage under the interpretation's graph is finite and not built. The cut with `==K`, all variables bound elsewhere, is read |
| `rangeMapPattern` | a range-map symbol binding a variable in a left side | always | `patternHooks`, `collPatternHooks` hold no range-map symbol | R-a: V6's reason (bounds, value and rest of unconfined sorts; the entry symbol silent at improper ranges). Not lifted by confining Int alone |
| `openLaw (assoc, idem)` | an open generator with both laws | always | `paramsPlain` | R-c (`lawHooks`): the two axioms have a model (the free band); its normal form is not built |
| `openLaw (unit)` | a unit law on an open generator | always | none needed: `ParamSig` has no field for it | R-c (`ParamSig`, `OpenLaws`, `lawHooks`) |
| `lawAxiom` | (i) an `[assoc]`, `[comm]`, `[unit]` or `[idem]` axiom on a `function` production that is no collection's concatenation; (ii) such an axiom on a symbol that kept `constructor` | always | none needed: nothing is added to `Γ` | (i) R-c (`Eval`): an equation between applications of a function, which no clause states. (ii) R-a: with a second constructor in the sort the axiom contradicts the no-confusion axioms; the text has no model (upstream list) |
| (a `raw` parameter with a hook, or a law on one whose signature is not `[s, s] → s`) | hand-built only; no text read has it | always | `paramsPlain` (V8) | suspected to leave `Γ` without a model |

`unboundVariable` and `existentialRhs` are interim reasons: after R1d, B1b and R2 a variable no left side binds is admitted or printed as `openRequires` or `openRight`.
`comm` on an open generator has no sentence in the text (kompile writes none), so nothing is read and nothing refused; the row in `rows.toml` says so.

**Reversal for the R-a rows that turn on a sort's extent** (`openExtent`, `openRequires`, `openRight` (i), `existentialEquation` (i), `openGeneratorPattern` (i)): a written sentence that states the sort's extent. Then `confined` grows by that case, with its axiom in `Γcl` and its values lemma in the manner of `boolClosed`, `boolValues`, `boolClosed_model`; this moves a pinned text's content (`Γcl`) and is a statement unit of its own.

**R-b:** any shape of the probes of brief P that kompile rejects, with its `kompile.txt`. Known: `e3-ml-rule-lhs-ceil` (a function symbol on a rewrite rule's left side under `#Ceil`), `e3-ml-eq-arg-not`.

**Not refused, a property of the text.** Each is read; the named fact is unprovable there, the account lists it as owed and open, and no theorem is stated while it is open:
- an equation whose instances differ, or clauses that disagree where an `aside` clause overlaps: `FnDet`, `ClausesAgree`, `MatchIndependent`;
- a closed condition over a variable no left side binds that no value witnesses and the theory does not refute (`f() => 0 requires 1 ==Int 2 *Int H`; a condition over a sort that reaches a sort without a generator): `CondDecided`;
- an interpretation that breaks a written law or leaves an open generator without a value: `OpenLaws`, `OpenTotal`; no statement is made at that interpretation;
- a total function without a value at some arguments: `FnHyp`'s second conjunct.
And one **text note** that is no owed fact: `overloadFunction` (F1), for a text whose function overload is not injective, total and apart at covered arguments; `Γ` reads the contradicted sentences at uncovered arguments and the note says the text has no model.

## 6. Change list for `[goal].statement`

The statement becomes a list of sentences (`statement = [ … ]`), in this order. "kept" items are the present text cut at its sentence boundaries, verbatim; the others are the exact text to put.

1. kept: "KCore (semantics-agnostic): every K construct of K 7.1.337 … proof tasks being uses of a definition and not part of it."
2. replace "What a package's semantics states is tied … and by sentence class." by three items:
   - "What a package's semantics states is tied to the KORE text sentence by sentence through the translation of the text, for every hook interpretation and by sentence class."
   - "For the sentences about hooked symbols, every hook interpretation is every admitted interpretation, under which each library sentence over the theory's symbols holds at values, set idempotence excepted (SILENT-TOTAL, SILENT-TOTAL-2)."
   - "For an open generator, a symbol the text declares functional with neither constructor nor hook: a law the text writes for it is a premise of the theory at every interpretation; its functional sentence is stated at values; and the package's statements are for every interpretation under which the laws and the functional sentence hold at values, OpenLaws and OpenTotal, two named obligations, with one such interpretation exhibited for each interpretation of the other symbols (HOOK-READING; CN-4 V1)."
3. replace, in "Function equations, rewrite rules, … or a member of a named family.", the words "a consequence of one" by "a consequence of translated sentences". (F6: the clauses of an `\or` right side follow from the equation together with the function's functional sentence.)
4. add after it: "One weakening is named beside those the account already records. For an overloading symbol one of whose overloads is a function, its functional, injectivity and distinctness sentences are stated at the arguments no overload covers; where the covering function is not total, injective and apart at covered arguments the text itself has no model, which the account notes and the theory does not refute (CN-4 F1). A sentence over a set variable read at singletons is not among them: it is refused."
5. add: "One premise rests on the builtin prose and is held only by a definition that reads a confined sort: every element of Bool is true or false (domains.md:1084; the family Γcl)."
6. add: "The theory does not carry the sorted logic's rule that every sort has an element; it entails an element at each sort with a value, and its exhibited model has none at a sort without one. At a constructor sort for which the text declares no generator the theory holds no no-junk premise, and no statement treats such a sort, or a sort that reaches it, as holding its values only (NONEMPTY, N1, CN-4 K1)."
7. add: "A condition closed over variables no left side binds, one of them of a sort the text leaves unconfined, is decided by the text where a value witnesses it or the theory refutes it; that fact (CondDecided, through OpenDecided) is an owed fact named with its rule or clause."
8. kept: "Sentences about hooked symbols (their functional axioms, the collection laws, the library's equations and lemmas) are stated at values only, kernel-checked where the row lists them and otherwise resting on the hook interpretations."
9. kept: "A sentence that applies a symbol the theory does not have … the initial configuration rests on the reader."
10. kept: "Set idempotence is the one sentence the theory refutes: the builtin prose for SET.concat is followed against it."
11. replace "The print-back check (Tied) is stated only for a text the emitter writes back up to order, which kompile's texts are not." by: "The print-back check (Tied) is stated only for a text the emitter writes back up to order, which kompile's texts are not; the tie of a sentence with a bound variable is on translated patterns, which carry no variable names."
12. kept: "The headline statements are pinned and axiom-free, … each reopening recorded."
13. kept: the Rows sentence ("Rows (semantics-specific, k2lean): … hypotheses listed.").
14. kept: the trusted-base sentence ("kompile's translation of K into KORE … recorded on the upstream list).").
15. kept: "Checked by designs/DONE-0-definition-of-done.md, criteria C1 to C14, at the tree named in core-manifest.toml."

Items 3 to 7 and 11 are required by decisions F6, F1, K1 with N1, V1 and R-D6; item 5 states what U1 built and the statement did not yet say; item 6's first sentence is N1's recommended wording.
Not changed: "Set idempotence is the one sentence the theory refutes" stays true (F1's weakening refutes nothing; V7's constructor idempotence is refused, not refuted).
`scoreboard_columns`, "owed facts": the names now include `CondDecided`, `OpenLaws`, `OpenTotal`.

## 7. Not decided, not read, to run

**Could not decide from the reading set.**
- CX-V D11: whether domains.md:498-500 ("contiguous or overlapping ranges that map to the same value are merged") is about concatenation. domains.md is outside the set. Until an owner reading of 498-504 with 600-602, `rmConcat` keeps the landed value (none at an overlap, equal values included) and the fixture asserts nothing at that term.
- d1's Lean (`sortOf`'s `keepsRaw` arm, `paramVal` at a `raw` parameter, `gens`, `consItemsK`): defined by CN-2 lines 276-336, outside the set. Section 4.7 names the passage and CN-4's amendments; the text itself is not restated here.
- The content of c2 and d2 beyond CX-V's rows, the K text of `e2-open-rule` (CN-2 §5), V1's six-step wiring plan (the V1 report): outside the set.
- Whether kompile accepts each probe of brief P (B3, `?B` in a function rule, `#Or` on an equation's right side, `[idem]` on a constructor production, an open generator across sorts, a non-linear set variable): the decisions are written for both outcomes.
- U0's own commit hash (it is inside `c1b90027`).

**R-c rows that CN-4 keeps or creates without a unit.** `[goal].direction` asks that every R-c construct be supported before R2 unless a first-principles reason stands. These have none and no unit here; whether each gets a design unit (with its own counterexample pass) or stays R-c at the freeze is the orchestrator's call: `#Or` on a non-total function's right side and more than 8 alternatives; an existential equation at a confined sort other than one Bool variable on a total function; `openRight` (ii), a variable held under a collection's symbols (`<m> K |-> ?V </m>`); a function-overloaded symbol in a pattern; `openGeneratorPattern` (ii); a non-linear set variable; `overloadAxiom` with a function as the larger symbol; `lawAxiom` (i); `openLaw (assoc, idem)`; `openLaw (unit)`.

**To run (stated here, proved by the unit named).** `confined_has_value` (CF-0); CX-R's `genless_not_sound` is no longer a target (K1 keeps the rule out of the theorems; its `CondDecided` is unprovable instead); for `e5-ovl-fun`: `coreOK`, `FnHyp`, `Consistent` (F3); the model cases of a function-overloaded symbol (F3); the three `OpenTotal` lemmas and the `…_withHooks` restatements (V2); the F6 and F4 tie lemmas (F2); every Lean block of section 4.9 (e3).

**Read for names and texts.** kcore-theory `8c2f206a`: FaithOK.lean (`litSort`, `confinedAt`, `confined`, `Cond.bound`, `ovlPairOK`, `overloadsOK`), Confined.lean (declaration list, `noJunkItem_mem`, `confinedAt_value`'s head, `confined_value`), Tie.lean (`…Plain`, `clauseSorted`, `condOK`, `ruleSorted`), Kore/Gamma.lean (`funItem`, `injItem`, `distItem`, `liesP`, `uncoveredP`, `distUncItem`), Kore/Translate.lean (`VarTable.index`, `freeOf`, `tableOf`), Definition.lean (`RulePres`), NICells.lean (`appOK`), test/Pins.lean (searches). kcore-symbolic `1fbee135`: Evaluation.lean (the `Eval` block), Faithful.lean (`clauseEquation` to `ΓFns`), Emit.lean (`exclusion`), Tie.lean (`clausesPlain`, `clauseSorted`), EvalFunctional.lean and FnSolves.lean (`Clause.AppliesAt`, `Coherent`, `MatchIndependent`, `FnSolves`, `PrioDecided`). kcore-reader `4c16f70f`: Tie.lean (`paramsPlain`), Faithful.lean (`consItemsK`, `ΓFallback`), Params.lean, ParamsTotal.lean (`totalParams`, `ParamsTotal`, `sortsOf_withHooks`), DefinitionWf.lean (`gens`, `patCtx`, `collPatSigs`, `patCtxAll`, `rhsCtx`). kcore-fix `1ac9b6e0`: Parse.lean (`RefusalReason`).
Beyond the brief's dates: the two "PICK UP HERE" entries of TICKETS (2026-11-15) came with the lines read; the RC-3 list in brief R1d is from them.
**Not read.** Every proof body; `distGuarded`, `norm`, `ovlOver`, `premise`, `eqnSentence`, `competingPremise` (their uses only); the model files; `ΓColls`'s axioms; Account.lean, KcoreGen.lean; kcore-kinds beyond what N1 quotes; kcore-merge at `0e4ddd03`; the fixtures' files (their sentences are taken from the CX files, which quote them). Other implementations: none consulted.

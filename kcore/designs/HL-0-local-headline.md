# HEADLINE: the statements KCore should freeze (Fable design agent, 2026-11-14)

Read-only design. Nothing was built or run. Lean text below is proposed text; items marked **to run** are for the orchestrator.
Trees read: released `kcore-merge` (`Sound`, `Statements`, `Step`, `Evaluation`, `ModelHas`, `ModelCarrier` 80-220, `FaithfulSound` 38-98, `Faithful` 519-630, `HypWf` 120-205, `CollExecFinal` 20-30 and 230-305, greps of `Model*.lean`), `kcore-tests` (`StepCompleteAt.lean`, `CS-2.md`), `kcore-kinds` (`SP-0` §1.4, §2.6-2.12, §3, §4, §6; `MODEL-LEMMAS.md`, found there, not in the main checkout), main checkout (`NF-1`, `KK-1` §1.4-1.6, `CS-0` §2.4-2.5, `REVIEW-SYNTH` OD-4..OD-10, `RE-0` §1, `REVIEW-ORDER` §5-6, `[goal]`).

## 0. The result in one paragraph

Three separate theorems replace the pair `sound_hyp` / `complete_hyp` as the headline, and the old pair stays, text unchanged, as corollaries.

1. **Sound at a step**: `coreOK` alone. It is already proved (`step_sound_core ∘ hypSound_of_core`); it only needs a name.
2. **Complete at a configuration**: `coreOK` and `StepDecided c x` (the `requires` of the rules no smaller priority blocks have results at `x`, and where true their right sides have results). No hypothesis on the functions of the definition, no model, no agreement.
3. **Consistent**: `Γ c ∪ Γstep c` has a model, under `coreOK`, `FnDet c` (results are unique) and `FnSolves c` (where a clause decides, the function's values are that clause's right side's). No termination conjunct and no totality conjunct.

`FnHyp` implies `FnDet ∧ FnSolves` and `∀ x, StepDecided c x`, so every theorem of today follows.
What the split buys: one bad corner of one function no longer silences the whole definition. KEVM's `senderTxData` (NF-1 F-K1) satisfies `FnSolves` as it stands; the 50 + 28 totality facts are read by no headline theorem; mir's type-table termination (NF-1 F-G3) is not asked; `kore.k` gets soundness and per-configuration completeness with its `hdef` as the only premise.
What it does not buy, and nothing can: five KEVM/mir clause pairs give two different values at one point (F-K8, F-K10, F-K12, F-M11, F-M12). There the text has no model, `FnDet` is false, and it must be false. That is a fact about those definitions (k2lean track: a guard, or a patch), not about the statement's form.

## 1. The statements

### 1.1 Definitions (new; cone)

```lean
/-- The rule applies at `x`: under some well-sorted σ its left side denotes `x` and its
`requires` evaluates to `true`. -/
def RuleApplies (c : Semantics) (r : Rule) (x : GroundTerm) : Prop :=
  ∃ σ, c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x ∧
    ∀ t, r.req = some t → EvalTerm c σ t (some (bool true))

/-- **The evaluations the step at `x` reads have results.** For every rule that no rule of a
smaller priority applies before: at each match of its left side, its `requires` has a result, and
where that is `true` its right side has one. (A result may be "undefined"; what is excluded is an
evaluation with no result at all.) -/
def StepDecided (c : Semantics) (x : GroundTerm) : Prop :=
  ∀ r ∈ c.rules, (∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x) →
    ∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧
      ((∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → ∃ v, EvalTerm c σ r.rhs v)

/-- The theory of `c`, with the step's closure, has a model. -/
def Consistent (c : Semantics) : Prop :=
  ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c)

/-- A function has at most one result at each argument list. -/
def FnDet (c : Semantics) : Prop :=
  ∀ f vs r r', Eval c f vs r → Eval c f vs r' → r = r'

/-- The clause decides at `vs` under σ: it applies there, and no clause of a smaller priority
applies there under any σ'. -/
def Clause.DecidesAt (c : Semantics) (fn : Fn) (cl : Clause) (σ : Subst) (vs : List GroundTerm) : Prop :=
  cl.AppliesAt c σ vs ∧ ∀ cl' ∈ fn.clauses, cl'.prio < cl.prio → ∀ σ', ¬ cl'.AppliesAt c σ' vs

/-- **Evaluation solves the equations**: where a clause decides, the values of the function are
the values of that clause's right side. -/
def FnSolves (c : Semantics) : Prop :=
  ∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∀ cl ∈ fn.clauses, ∀ σ,
    cl.DecidesAt c fn σ vs → ∀ v, Eval c fn.label vs (some v) ↔ EvalTerm c σ cl.rhs (some v)
```

With `Rule.ens` (RE-0) the last conjunct of `StepDecided` also asks a result of the `ensures`: `… → (∃ v, EvalTerm c σ r.rhs v) ∧ ∀ e, r.ens = some e → ∃ w, EvalTerm c σ e w`.

### 1.2 Theorems (headline)

```lean
theorem sound_at (c : Semantics) (h : c.coreOK = true) (x y : Config c) (hs : Step c x y) :
    Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val))

theorem complete_at (c : Semantics) (h : c.coreOK = true) (x : Config c) (hd : StepDecided c x.val)
    (ys : List GroundTerm) (hys : ∀ y : Config c, Step c x y → y.val ∈ ys) :
    (Γ c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (ys.map (den c))))

theorem consistent_of (c : Semantics) (h : c.coreOK = true) (hd : FnDet c) (hs : FnSolves c) :
    Consistent c
```

Soundness has no hypothesis at `x` because the derivation `Step c x y` already holds every evaluation it needs.
Agreement does not appear at `x`: `complete_at` is an entailment, and in a model of `Γ` each derivation's result is the term's denotation (`evalTerm_den4`), so two results of one evaluation cannot coexist with a model.

### 1.3 Corollaries (text of today's statements unchanged)

```lean
theorem fnModel_of_fnHyp (h : c.coreOK = true) (hf : FnHyp c) : FnDet c ∧ FnSolves c
theorem stepDecided_of_fnHyp (h : c.coreOK = true) (hf : FnHyp c) (x : Config c) : StepDecided c x.val
theorem sound_hyp   …  : SoundC c            -- consistent_of ∘ fnModel_of_fnHyp, sound_at
theorem complete_hyp … : CompleteC c ref     -- complete_at ∘ stepDecided_of_fnHyp, at ys := ref x.val
-- the consumer's form, at the fuel it ran (uses what CollExecFinal already has):
theorem CExec.stepDecided_of_fuel (hr : execReady c = true) {n} {x : Config c}
    (hf : outOfFuel c n x.val = false) : StepDecided c x.val
theorem CExec.run_exact (h : c.coreOK = true) (hr : execReady c = true) (hd : FnDet c) {n} {x : Config c}
    (hf : outOfFuel c n x.val = false) :
    ((Γ c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((successorsN c n x.val).map (den c))))) ∧
    ∀ y ∈ successorsN c n x.val, Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y))
```

`run_exact` is what a package user holds for one configuration: run the checked executor, and if nothing ran out of fuel the listed successors are exactly what every model of the theory has.
`hd : FnDet c` there can go if finding 4 proves (`Consistent c → FnDet c`; when there is no model both entailments hold vacuously).

### 1.4 Sufficient conditions for `FnSolves` (library, not cone)

```lean
/-- Where a clause applies, each `requires` of a matching clause of a smaller priority has a result. -/
def PrioDecided (c : Semantics) : Prop :=
  ∀ fn ∈ c.fns, ∀ vs cl σ, cl ∈ fn.clauses → cl.AppliesAt c σ vs →
    ∀ cl' ∈ fn.clauses, cl'.prio < cl.prio → ∀ σ', c.WellSorted cl'.vars σ' → PatVals c σ' cl'.pats vs →
      ∀ t, cl'.req = some t → ∃ r, EvalTerm c σ' t r
/-- Two clause instances that decide at one point: if one right side has a value, the other has a result. -/
def CoDefined (c : Semantics) : Prop :=
  ∀ fn ∈ c.fns, ∀ vs cl σ cl' σ', cl ∈ fn.clauses → cl' ∈ fn.clauses →
    cl.DecidesAt c fn σ vs → cl'.DecidesAt c fn σ' vs →
    (∃ v, EvalTerm c σ cl.rhs (some v)) → ∃ r, EvalTerm c σ' cl'.rhs r
theorem fnSolves_of_parts (h : c.coreOK = true) (hd : FnDet c) (hp : PrioDecided c) (ha : CoDefined c) : FnSolves c
```

Argument (by reading). Take `cl, σ` deciding at `vs`. `PrioDecided` turns "no smaller priority applies" into `Fails` for each such clause, so `Eval.clause` gives `Eval f vs r` for every result `r` of `cl.rhs` under σ (←). For (→), a value `v` of `f` comes from a clause instance `cl₂, σ₂`; it is not of smaller priority (`cl` decides), not of larger (its `hprio` gives `Fails c vs cl`, against `cl` applying, by `FnDet`), so it decides too; `CoDefined` gives `cl.rhs` a result `r`, `Eval f vs r` by (←), and `FnDet` makes `r = some v`.
Both are empty for most functions: `PrioDecided` is vacuous for a function with one priority, and decidable where the `requires` of the non-last priorities apply hooks or functions with a termination certificate; `CoDefined` is vacuous where `fnExclusiveOK` and `clauseFixed` already confirm that two deciding instances are the same instance.

### 1.5 Why these, from first principles

**(a) `StepDecided` is needed, and is the least the proof reads.**
`step_complete_at` uses its `HypModelCore` hypothesis in four places only (StepCompleteAt.lean:37, 91, 157, 178, 185): `h.sound` (from `coreOK`), `Model.freeOf_prio h` (reads `h.hyp.1 = sortedOK` only, ModelStep.lean:169-170), and `Model.evalTerm_total h` three times: the chosen rule's `requires`, a competitor's `requires`, the chosen rule's right side. No use of coherence. Replacing the three by `StepDecided` needs one reordering: first, from `hcomp` and `applies_holds`, no rule of a smaller priority than the chosen one `RuleApplies` (so the chosen rule and each of those is unblocked in `StepDecided`'s sense); then the three results.
Needed: with `a => b requires loop(0)` and `loop(X) => loop(X)`, `Γ ∪ Γstep` has a model where `loop(0)` is `true` (and `a` steps to `b`) and one where it is not; `Step` has no step from `a`. So `⟦a⟧ → ◦⊥` is not entailed, and no condition weaker than "that `requires` has a result" restores it. (Finding 2, to run.)
The "unblocked rules only" form, rather than "every rule that matches", is what `kore.k`'s `hdef` gives after its unit B (KK-1 §1.4, last paragraph); the all-rules form is the corollary `outOfFuel = false` gives.

**(b) The model needs something global, and termination is not it.**
The value model interprets `f(vs)` as `{v | Eval c f vs (some v)}` (ModelCarrier.lean:155-160): defined for every semantics, empty at a point with no derivation. The proof that it satisfies `Γ` reads `evalTerm_total` at exactly three places: ModelFns.lean:369 (the `requires` of clauses of smaller priority: `PrioDecided`), ModelFns.lean:398 (the right side of the deciding clause: `CoDefined`), ModelPat.lean:796 (`applies_iff`, a competitor rule's `requires`). The first two are `FnSolves` unfolded at one equation; the third disappears if the model's `next` is read with "no rule of a smaller priority `RuleApplies`" in place of `NotApplies` (a definition inside the model, not in the cone; the two agree wherever `StepDecided` holds).
`FnHyp`'s second conjunct (`[total]` functions have values) is read by no proof of `has_model_core`, `step_sound_core` or `step_complete`: its only reader is `totalRead_of_hyp` (FaithfulStage4.lean:506), used on the older `Hyp` route (FaithfulColl.lean:983), and `ModelFunctional.lean`. `Γ` holds no functional axiom, so nothing in the headline reads `[total]`.
Something global is needed: `f(X) => 1 requires f(X) ==Int 2 [priority(40)]`, `f(X) => 2 [owise]` has no model (if `f(v) = 2` the first equation gives 1; otherwise the second gives 2). `FnSolves` is false there, as it must be. (Finding 3, to run.)
`FnDet` is necessary for any model (two results give `⟦a⟧ = ⟦b⟧` in every model, by `eval_den4`). `FnSolves` is exactly "the value model satisfies the equations at ground points", so it is the weakest condition for this model; a definition can be consistent without it (a `requires` of a smaller priority that diverges while another model picks a value), and for such a definition KCore's reading by evaluation is not a model of the text, so no theorem relating `Step` to `Γ` should be non-vacuous there.
Both are stated for every semantics, over `Eval` only, read no presentation and no certificate.

**(c) What `Γ` then entails where evaluation gives nothing.**
- At a point with no derivation (non-termination): only what the equations say (`senderTxData`: `f(0) = f(27)`); neither `⊥` nor a value. `Step` has no derivation through such a call, `StepDecided` fails at the configurations whose step reads it, and the theorems are silent exactly there.
- At a point where every clause fails, with group C (OD-4 (iii)): `f(vs)` is the interpretation's value, `⊥` where it gives none; over all interpretations nothing but the sort.
- At a hook's `⊥` point (class U): `⊥`, as today.

**(d) Does group C's fallback let the model exist without global termination or agreement?** No. `Eval.rest` still needs `Fails` of every clause, a derivation; it changes what an uncovered point is, not whether a point has a result. What removes global termination is (a) and (b). Group C removes a different defect: the closure axiom makes `Γ` state `⊥` where the text does not, and for KEVM that contradicts a sentence of the text (§3, simplification axioms).

## 2. What changes

### 2.1 Cone

| Declaration | Change |
|---|---|
| `RuleApplies`, `StepDecided`, `Consistent`, `FnDet`, `Clause.DecidesAt`, `FnSolves` | new, about 30 lines |
| roots | `sound_at`, `complete_at`, `consistent_of` statements, `coreOK`; in place of `SoundC`, `CompleteC`, `StepIs`, `FnHyp` |
| `FnHyp`, `ClausesAgree`, `Coherent`, `MatchIndependent`, `HDet`, `Fun`, `subterms`, `varOccs`, `pairs`, `StepIs`, `StepFn`, `CompleteC`, `SoundC` | leave the cone (`core-cone.txt` lists them "via FnHyp / Coherent / CompleteC"); they stay in the library, text unchanged |
| `Clause.AppliesAt` | stays (via `DecidesAt`) |
| `Step`, `NotApplies`, `Eval`, `Γ`, `Γstep` | unchanged by this design (group C and `Rule.ens` change them on their own tickets) |

Net: the cone shrinks. No existing statement is weakened; the new theorems have weaker hypotheses and the old ones are derived from them.

### 2.2 Proofs (estimates from the files, not measured)

| Unit | Files | Size |
|---|---|---|
| `complete_at` from `HypSoundCore` + `StepDecided` | `StepCompleteAt.lean` (the 160-line proof, three sites and the reordering), `freeOf_prio` restated over `sortedOK` | 60-90 lines changed |
| `stepDecided_of_fuel` | `CollExecFinal.lean`, from `of_outOfFuel_false`, `evalT_sound`, the match completeness `hrc` | 60-100 new |
| `EvalTerm.functional` from `FnDet` | new lemma by induction on the term | 60 new |
| model under `FnDet ∧ FnSolves` | `ModelCarrier` (`StepE`), `ModelPat` (`applies_iff`, 17 `hmi` sites across ModelPat/ModelFns), `ModelFns` 369, 398, `ModelRules.rhs_next`, `ModelStep`, `HypWf.hypModel_of_fnHyp` | 300-500 changed |
| `fnModel_of_fnHyp`, `stepDecided_of_fnHyp`, `fnSolves_of_parts` | new, beside `HypWf` | 150 new |
| `Coherent` with the "no smaller priority applies" premise (§3), `Eval.functional` re-proved | `EvalFunctional.lean` | 30-60 changed |

About 800 to 1,200 lines, three Opus briefs. The risk is in the model unit (the `hmi` sites); the first unit is nearly mechanical.

### 2.3 Deciders and named facts

`CoreObligations` today is five lists whose conjunction gives `FnHyp`. Proposed: the lists stay as outputs of the generic deciders (KCore), and what they are premises *of* changes.

| List | Today | Becomes |
|---|---|---|
| agreement (`agreeObligations`), match (`matchObligations`) | `ClausesAgree`, `MatchIndependent` | sufficient for `FnDet` (and with exclusivity, `CoDefined`); the only lists `consistent_of` needs for a one-priority definition |
| termination (`orderObligations`, certificate) | every function, every argument | restricted to the functions called in a `requires` of a clause that has a sibling of larger priority (→ `PrioDecided`). The full list is premise only of the optional `∀ x, StepDecided c x`, which gives `CompleteC` back |
| totality (`totalObligations`) | `FnHyp` conjunct 2 | premise only of the optional `has_model_total` (`Γ ∪ Γstep ∪ ΓTotal`, MODEL-LEMMAS §1), with `RestTotal` after group C |
| lazy (`lazyObligations`) | not read by `fnHyp_of_core` | unchanged |
| per configuration | none | `StepDecided c x`: discharged by a run (`stepDecided_of_fuel`), by a k2lean bridge (the generated `F.eval` lemmas give the results), or for `kore.k` by `hdef` |

Which facts a package must discharge is then per definition (k2lean): `FnDet` and `FnSolves` once, `StepDecided` at the configurations its theorems speak about.

## 3. Decisions revisited

Each: decision, reason, what would reverse it.

**OD-7, R-block: keep.**
A rule's own axiom has its left side and `requires` on the left of `\rewrites`; the competitor premise that names exactly that is the only one that is the left side of an axiom of the text (`block_comp_lhs_req`). Under the per-configuration statements R-block is also the smaller hypothesis: `StepDecided` asks no right side of a blocked rule and none of a rule that blocks; R-skip would make `NotApplies` read right sides, so every smaller-priority right side would have to have a result before any step is decided. Cost was not the reason in RE-0 and is not here.
Reverse: RE-0 §1.5's three conditions, unchanged.

**OD-4, fallback for every function (iii): keep, and it must land before the freeze, for all functions, not only `[total]` ones.**
New reason beside "asserts no more than the text": KEVM's text states `` `_<Gas_`(infGas(_), _) = false `` as an axiom (tagged `simplification`, NF-1 F-K4); `Γ` with the closure axiom proves `infGas(0) <Gas 0 = ⊥`. So today `Γ` contradicts a sentence of the text it reads. With the rest, that sentence is a condition on the interpretation.
A fourth reading was considered and rejected: no `Eval.undef` at all, an uncovered point having no result like a diverging one. It is consistent with §1's statements, but every configuration whose step reads an uncovered call is then outside `StepDecided`, including every `[owise]` that relies on a partial function failing; (iii) gives a decided step for each interpretation and today's runs at the one that gives no value.
Consequence to accept: mir's `lookup*Kore` under (iii) make termination depend on the interpretation (F-G3). Under §1 that costs nothing: no theorem asks global termination.
Reverse: SP-0 criteria 1, 2, 4 as in OD-4; or `consistent_of` failing to prove with `Eval.rest` (the rest graph's side condition `∀ cl, Fails c vs cl` is a derivation, so it should be read by the model as `Eval.undef` is today).

**No clause at all (`functional`, no equation; mir `lookup*Kore`): the case `clauses = []` of (iii), no separate rule.**
NF-1 F-M1 found the tree it read giving these `none` (`Eval.undef` vacuously). Under (iii) the rest is the interpretation's value for every function, so "parameter when there is no clause, closure when there is one" (S8) is gone. The text's `functional` axiom is then `RestTotal` on the interpretation, read only by `has_model_total`.
Reverse: none beyond OD-4's.

**OD-8, priorities read into every rule and equation, `⌈rhs⌉` in a rule's premise: keep; one addition.**
`⌈rhs⌉` is forced (without it a matched configuration with an undefined right side has a successor in the empty set). Priorities as negated competitors are the only reading under which the attribute acts. The addition: they are also the only source of non-monotonicity in `Γ`, hence the only reason `FnSolves` is not automatic (§1.5 (b)'s counter-example needs two priorities). Write that sentence in the "`Γ` and the text" table: "a definition with one priority per function needs only `FnDet` for a model". The two negative theorems (W-a) stay as planned.
Reverse: W-a's theorems failing, as in OD-8.

**`ClausesAgree` strength (NF-1 F-G1): change.**
`Coherent` gets the premise "no clause of a smaller priority applies at `vs`" (`DecidesAt` for both clauses). It leaves the cone under §2.1, so the change costs no frozen text. `Eval.functional` cannot need agreement at a shadowed point: each `Eval.clause` derivation carries `hprio` for its own clause, so two derivations at one priority both have every smaller priority failing (suspected; settle by re-proving `case_clause`, 30-60 lines). F-M14 disappears; the five real contradictions do not.
Reverse: `case_clause` needing more.

**`simplification` axioms: do not read them as clauses; do not add them to `Γ`.**
They may overlap each other and the definitional equations, and the text gives them no priority; reading them as clauses would make `Eval` depend on an order the text does not state. Left out of `Γ` they cost nothing: soundness is proved from fewer axioms, completeness is monotone in axioms. Their content is recovered as a condition on the interpretation at rest points (k2lean, per definition: "the interpretation satisfies the definition's simplification axioms"), which under (iii) is satisfiable and under closure is not (above).
Reverse: a definition whose simplification axiom constrains a point a clause covers with a different value (then the text is inconsistent and the question is moot), or a reader need to count them as "read" (scoreboard wording: "inert, with the reason").

## 4. The split

**KCore (holds for every definition).**
Kernel: `Semantics`, `Eval`, `Step`, hooks and silent points (SP-0 A, B, C, D), `Rule.ens` (RE-0), carrier gaps (Float field 1, surrogates), collections' axioms (FD-C).
Statements: §1; `Γ`, `Γstep`, `ΓTotal`; the "`Γ` and the text" table; W-a, W-b negative theorems; MODEL-LEMMAS.
Reader: `Parse`, account, corpus runs, OV-6, RD tickets; differential runs of the executor against recorded outputs.
Generic deciders and their soundness: `coreOK`, `totalOK`, `fnExclusiveOK`, `clauseFixed`, rank certificates, `execReady`, `outOfFuel`, `stepDecided_of_fuel`, `fnSolves_of_parts`, the list emitters (`kcore fn-facts`).
Consumer interface: `Bridge` / `Transfer` (CS-2), `SymbolicLemmas`, `insertE_mem`, `sortOf_isInj`, the `pv_*` / `ev_*` introduction forms, `Eval.sortPred`, `Eval.calls_induct` (KK-1 §1.5), `run_exact`.
The package generator's generic part (what every package states) and the docs course.

**k2lean (one definition).**
Each package and its kernel build: ref-kimp, KEVM, wasm, mir, `kore.k`.
Discharging or refuting named facts: NF-1's 94 + 50, NF-3; definition-side patches for F-K8, F-K10, F-K12, F-M11, F-M12; conditions on the interpretation (`RestTotal`, `ParamsTotal`, simplification axioms, a well-founded type table).
Bridges: `enc`, `Wf`, `F.eval`, `Rules.ρ.fwd/bwd` generation (CS-3), invariants (`ImpWrites`, `kevm-inv`).
KORE in K: `kore.k`, `encDef`, `succs_sound` / `succs_complete` / `succs_stuck`, `eval_spec`, `KK.coherent`, kink mutations. `succs_complete`'s `hco : CoherentAll d` becomes `FnDet d`.
The per-definition scoreboard of `[goal]` (rows imp, KEVM, wasm, mir, KORE in K).

**KCore's own scoreboard** (proposed columns: read by the reader / meaning in `Eval` or `Step` / axiom in `Γ` / in the value model / in `sound_at` and `complete_at` / decider). Status as far as the reading set shows; "?" is not known to me and needs the orchestrator's numbers.

| K construct | State |
|---|---|
| sorts, subsorts, injections, constructors | all columns met |
| overloads | met; `overloadsOK` provisional in `coreOK` |
| Int, Bool hooks | met |
| String, Bytes hooks | met at U points; S and T points pending SP-0 B |
| Float | 5 operations interpreted, 16 parameters; field-1 formats pending |
| MInt, sort parameters | not read (KN-4, KN-5); ? |
| Map, Set, List, cell maps | met; whether `Γ` entails assoc / comm / unit pending FD-C |
| function equations, `requires` | met |
| priorities, `[owise]` on equations | met; needs `FnSolves` for the model (§1.5 (b)) |
| uncovered points | closure today; rest pending SP-0 C |
| `[total]` / `functional` | not in `Γ`; `ΓTotal` beside it (MODEL-LEMMAS §1) |
| function with no equation | pending SP-0 C (§3) |
| `ensures` on an equation | read as a `requires` conjunct; re-check after C (S19) |
| `simplification` axioms | not read; stated as inert (§3) |
| non-terminating evaluation | no result; theorems silent exactly there (§1.5 (c)) |
| rules, `requires`, priorities | met |
| `ensures` on a rule | pending RE-0 |
| undefined right side | met (`⌈rhs⌉`, R-block) |
| parameter symbols | met for every interpretation |
| claims, symbolic patterns in rules | ? (refused, I believe) |

Statements row: `sound_at` proved (unnamed); `complete_at` proved under `FnHyp` (`complete_at_hyp`), to re-prove under `StepDecided`; `consistent_of` proved under `FnHyp` (`has_model_core`), to re-prove under `FnDet ∧ FnSolves`.

## 5. Order

No further Fable design is needed for §1 and §2. One small Fable check is needed after group C and `Rule.ens` land: re-read `StepDecided`, `FnSolves` and the rest graph together (the `ens` conjunct; `Eval.rest` in `FnSolves`' model proof) before the cone is frozen.

Before the freeze, in this order (A and group C1 touch disjoint files and can run together; B after C because both edit `ModelFns`; `Rule.ens` E1 after A because both edit the completeness proof):

**Brief HL-A (Opus, three units): the per-configuration pair.**
1. `RuleApplies`, `StepDecided` (end of `Step.lean`); `step_complete_at` re-proved from `HypSoundCore c` and `StepDecided c x.val`; `freeOf_prio` over `sortedOK`; `complete_at`, `sound_at` in `Sound.lean`; `complete_at_hyp` and `complete_hyp_of_at` kept as corollaries through `stepDecided_of_fnHyp`.
2. `CExec.stepDecided_of_fuel`; `CExec.run_exact` with `hd : FnDet c` (through `step_iff_at`, whose `CoherentAll` hypothesis is replaced by `FnDet` in unit HL-B1; until then with `CoherentAll`).
3. Tests: finding 2's witness; `CS2`'s `impWrites_next` restated through `complete_at` with no `FnHyp`.
Stop and report if `step_complete_at` reads anything of `HypModelCore` beyond the four places listed in §1.5 (a).

**Brief HL-B (Opus, three units): the model.**
1. `FnDet`; `EvalTerm.functional` from `FnDet`; every `CoherentAll_of h.hyp` site in `Model*.lean`, `CollExecFinal`, `CollExecStepIff` takes `FnDet`; `Coherent` gains the `DecidesAt` premise and `Eval.functional` is re-proved, giving `fnDet_of_coherent`.
2. `Clause.DecidesAt`, `FnSolves`; the model's `next` read by `RuleApplies`; ModelFns 369 and 398 and ModelPat 796 without `evalTerm_total`; `consistent_of`.
3. `fnModel_of_fnHyp`, `fnSolves_of_parts`, `PrioDecided`, `CoDefined`; `sound_hyp`, `complete_hyp`, `sound_core`, `complete_core`, `sound`, `complete` and the `withHooks` forms re-derived, their text unchanged; finding 3's witness.
Stop and report if the value model needs a fact about a point no clause decides.

**Brief HL-C (Opus, two units, after B): what the deciders and packages state.**
1. `kcore fn-facts` emits the restricted termination list (§2.3) and counts, natively, for KEVM and mir: how many functions have more than one priority, how many `PrioDecided` and `CoDefined` facts remain.
2. The generated package states `sound_at`, `complete_at`, `run_exact` and, under its listed facts, `Consistent`; the `∀ H` form (SP-0 D3).
Optional third unit: finding 4 (`Consistent c → FnDet c`), only if values have distinct elements in every model of `Γ` by an existing lemma.

Also before the freeze, already planned and unchanged by this design: SP-0 B and C (C with `fnRest` for every function), RE-0 E1 and E2, W-a, W-b, W-c, FD-C's verdict. REVIEW-ORDER §5 row 10 ("a pointwise form of `FnHyp`'s first conjunct") is this design; row 11's totality axiom stays outside `Γ`.

## 6. Findings

1. **`sound_hyp`'s step half already holds with no function hypothesis.** `Sound.lean:50`: `step_sound_core c (hypSound_of_core h)` takes `h : c.coreOK = true` only. Shown by reading. Settle: name it (`sound_at`).
2. **`StepDecided` cannot be dropped from completeness.** Claim: for `a => b requires loop(0)`, `loop(X) => loop(X)` (`loop : Int → Bool`), `coreOK` holds, `Step` has no step from `a`, and `Γ ∪ Γstep ⊭ ⟦a⟧ ⇒ ◦⊥`. Suspected (the model with `loop(0) = true` and `a → b` satisfies the equation `loop(X) = loop(X)`, the closure axiom `y ∈ loop(X) → y ∈ loop(X)`, the rule and the step's closure). **To run**: build the semantics `loopD`; prove `¬ ∃ y, Step loopD a y` by `Eval.rec` (no derivation of `Eval loopD loop [0] r`), and exhibit the interpretation (the value model with `result` overridden at `loop [0]` to `{true}` and `next` extended by `a → b`).
3. **Some global condition is necessary for a model, and `FnSolves` detects it.** Claim: for `f(X) => 1 requires f(X) ==Int 2 [priority(40)]`, `f(X) => 2 [owise]`, `Γ` has no model, `FnDet` holds (no derivation at all) and `FnSolves` fails. Suspected. **To run**: `theorem paradox_no_model : ∀ M _ I, ¬ (I ⊧ᴵP Γ paradoxD)` (cases on whether `⟦f(0)⟧ = ⟦2⟧` in `I`, the two equations read at `X := 0`), and `¬ FnSolves paradoxD`.
4. **`Consistent c → FnDet c` under `coreOK`.** `eval_den4` (FaithfulStage4.lean:874) gives `⟦f(ws)⟧ = Res r` in every model for every derivation; two results differ in a model if distinct sorted values have distinct elements. Suspected; I did not find a lemma that `elemOf c I` is injective on sorted values (maps and sets included). Settle: that lemma, or a counter-model; if it holds, `run_exact` needs no `FnDet`.
5. **`FnHyp`'s totality conjunct is read by no headline proof.** Evidence: the only projection of it is `hy.2.2.2.1` at FaithfulStage4.lean:506 (`totalRead_of_hyp`), whose only caller is FaithfulColl.lean:983; `step_sound_core` and `step_complete_at` build `TotalRead` from `exclusion_emptyC`. Shown by grep, not by reading every proof. Settle: delete the conjunct from a copy of `HypCore` and rebuild.
6. **The model reads termination at three sites.** ModelFns.lean:369, 398; ModelPat.lean:796. Shown by grep (`evalTerm_total`, `fn_total`). Settle: HL-B unit 2.
7. **KEVM's text and the closure axiom contradict each other at `infGas(0) <Gas 0`.** From NF-1 F-K4 (`definition.kore:40844`), not re-read by me. Suspected. Settle: with the axiom added to `Γ kevm`, the value model fails it; one `decide`-style evaluation of `_<Gas_` at that point.
8. **Five clause pairs make `FnDet` false for KEVM and mir as written** (NF-1 F-K8, F-K10, F-K12, F-M11, F-M12). No statement form repairs this; `sound_at`, `complete_at` and every `Step`-level theorem still hold, the entailments vacuously. Owner decision: whether a patched definition, or the definition restricted by a guard, is the scoreboard row.
9. **`step_iff_at` and `succs_complete` ask `CoherentAll`; `FnDet` is what they use.** `CollExecFinal.lean:279, 287`: both uses are `EvalTerm.functional hco`. Shown by reading those lines. Settle: HL-B unit 1.

## Not read

`ModelFns`, `ModelPat`, `ModelRules`, `ModelStep`, `FaithfulComplete`, `FaithfulStage4` beyond the lines cited (statements and greps only); `EvalFunctional.lean` beyond 28-40, 120-175, 342-358 (so finding F-G1's settlement is suspected, not shown); `Hooks.lean` (the `hookRes` lemmas in `Evaluation.lean` were read instead); `CS-0` §2.1-2.3; `KK-1` §1.1-1.3; `core-manifest.toml`; the deciders; any package; `TICKETS` beyond `[goal]`.
The line estimates of §2.2 come from file sizes and grep counts.

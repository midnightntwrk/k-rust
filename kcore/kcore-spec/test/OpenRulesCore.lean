/-
  The lemmas over rules and clauses with open variables, at semantics that `coreOK` accepts and that
  have a rule whose left side leaves a variable open. Run from the package root:
  `lake env lean test/OpenRulesCore.lean`. Kernel-checked (`decide +kernel`).

  - `cO`: the reader's semantics for `f2-examples/symrule.kompile.kore` (as `test/OpenRules.lean`)
    with the rules `ok1` (`a() => b(X)`, X:Int, arm A), `okB` (`a() => a() ensures B`, B:Bool, arm
    B), `ok2` (`a() => a() requires H ==Int 0`, H:Int, arm C, `needsWitness`), `okBc`
    (`a() => a() requires B`, B:Bool, an open condition variable of a confined sort), `ok4`
    (`a() => b(X) requires H ==Int 0`, X by arm A, H by arm C, passing the competition conjunct by
    closed conditions) and `plain` (`a() => a()` at priority 200, larger than each). `cO` has `coreOK` and reads a confined sort
    (`readsConfined`), both decided. `ok2` and `ok4` are `Witnessed` at H := 0, and no other rule or clause of
    `cO` needs a witness, so the hypotheses `hw` and `hc` of the lemmas are proved at `cO`, not
    assumed. Instantiated there: `rule_step_valuesSSx` (each of `ok1`, `okB`, `ok2`), `rule_subst_AB`
    (`okB`), `sat_rule_open` and `applies_iff_open` (each rule of `cO`); and the pinned theorems at
    `cO` from `coreOK` alone: `sound_at`, `complete_at`, `consistent_of`, `exact_hyp`,
    `has_model_choice`, `famOpen_values` (at `okB`); `sound_at` also at a step by each of `ok1`,
    `okB`, `ok2`, `ok4`.
  - `cOC`: the reader's semantics for `f2-examples/opencl.kompile.kore` (as `test/OpenClauses.lean`)
    with the rule `rB` (its rule with B:Bool open, held by the `ensures` only). `cOC` has `coreOK`
    and reads a confined sort. `exclEmptyCl_of` at `clB` (`g(X) => 1 requires B`: its premise that
    the definition reads a confined sort holds at `cOC`), at `clP` and at `clW`
    (`g(1) => 1 requires H ==Int 0`, H:Int, `needsWitness`, `Witnessed` at H := 0, so
    `CondDecided` is proved); `exclEmptyCl_core` at `clW`. The clauses are not `cOC`'s:
    `exclEmptyCl_core` asks every clause of the definition to bind its variables in its patterns
    (`hbc`), which a definition holding `clW` does not (`cOW` below).
  - `cOW`: `cOC` with `g`'s clauses `clW` and the `[owise]` clause. `coreOK`; `clW` `Witnessed`, so
    `OpenDecided` (`odOW`); with `FnFacts` (the one named fact, `clW`'s match independence, by
    hand: `miW`) `fnHyp_of_fnObligations` gives
    `FnHyp cOW`, hence `StepDecided` at every configuration, `FnDet`, `FnSolves` and `Consistent`,
    and the pinned `sound_at`, `famEx_closed`, `complete_at`, `consistent_of` there with every
    hypothesis on the definition proved. `complete_at`'s `hval` and `hfam` (the outcomes of the
    successors) stay hypotheses on the configuration. `hbc` is false at `cOW` (`not_hbcOW`): the
    missing fact for `exclEmptyCl_core` there is `ModelFailsCl` from `Fails`, which
    `modelFailsCl_of_core` derives through `hbc`.
  - Not instantiated non-vacuously: `CondDecided` at `test/OpenClauses.lean`'s `clH`
    (`f() => 0 requires 1 ==Int 2 *Int H`) and `clG` (`g(X) => 1 requires isC(H)`, H:S). Neither is
    `Witnessed`: no Int value solves `1 = 2 * H`, and S has no value (`opencl.k`: its one generator
    takes a sort without values). Neither is `Refuted` by any argument here: Int and S are not
    confined, so `Γc` holds no axiom that excludes an element where the condition holds.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace OpenRulesCore

/-! ## Rules: `cO` -/

namespace R

definition_of defn from "f2-examples/symrule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def i (n : Int) : Term := .dv Srt.int (.int n)
/-- `<generatedTop>(<k>(kseq(inj{Exp,KItem}(b), V0)), cnt)`. -/
def cfg (cnt : Term) : Term :=
  .app 71 [.app 383 [.app 0 [.inj 32 1 (.app 386 []), .var 0]], cnt]

noncomputable def sK : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 1 0
noncomputable def sC : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 2 0

noncomputable def mk (vars : List Srt) (rhs : Term) (req ens : Option Term) (prio : Nat) : Rule :=
  { vars := vars, lhs := cfg (.var 1), req := req, rhs := rhs, ens := ens, prio := prio }

/-- `a() => b(X)` -/
noncomputable def ok1 : Rule := mk [sK, sC, Srt.int] (cfg (.app 73 [.var 2])) none none 50
/-- `a() => a() ensures B` -/
noncomputable def okB : Rule := mk [sK, sC, Srt.bool] (cfg (.var 1)) none (some (.var 2)) 50
/-- `a() => a() requires H ==Int 0` -/
noncomputable def ok2 : Rule := mk [sK, sC, Srt.int] (cfg (.var 1)) (some (.app intEq [.var 2, i 0])) none 50
/-- `a() => a() requires B` -/
noncomputable def okBc : Rule := mk [sK, sC, Srt.bool] (cfg (.var 1)) (some (.var 2)) none 50
/-- `a() => b(X) requires H ==Int 0` -/
noncomputable def ok4 : Rule := mk [sK, sC, Srt.int, Srt.int] (cfg (.app 73 [.var 2])) (some (.app intEq [.var 3, i 0])) none 50
/-- `a() => a()` at priority 200 -/
noncomputable def plain : Rule := mk [sK, sC] (cfg (.var 1)) none none 200

/-- The text's semantics with the six rules. -/
noncomputable abbrev cO : Semantics := { c with rules := c.rules ++ [ok1, okB, ok2, okBc, plain, ok4] }

/-- **`cO` has `coreOK`, reads a confined sort, and four of its rules leave a variable open.** -/
theorem coreO : cO.coreOK = true ∧ cO.readsConfined = true ∧
    ok1.opens = [2] ∧ okB.opens = [2] ∧ ok2.opens = [2] ∧ okBc.opens = [2] ∧ plain.opens = [] := by
  decide_cheap

/-- The rules' facts, and which arm each open variable passes. -/
theorem facts :
    (cO.ruleSorted ok1 = true ∧ cO.rulePlainOpen ok1 = true ∧ ok1.opens.all (ok1.armAB cO) = true) ∧
    (cO.ruleSorted okB = true ∧ cO.rulePlainOpen okB = true ∧ okB.opens.all (okB.armAB cO) = true ∧
      (ctorOccs cO okB.rhs).contains 2 = false) ∧
    (cO.ruleSorted ok2 = true ∧ cO.rulePlainOpen ok2 = true ∧ ok2.opens.all (ok2.armAB cO) = false ∧
      ok2.condVars = [2] ∧ ok2.reqClosed = true) ∧
    (cO.ruleSorted okBc = true ∧ cO.rulePlainOpen okBc = true) := by
  decide +kernel

/-- Which open variables are of a confined sort: `okB`'s and `okBc`'s (Bool); not `ok1`'s or `ok2`'s
(Int). -/
theorem conf :
    ok1.opens.any (fun i => (ok1.vars[i]?.map cO.confined).getD false) = false ∧
    okB.opens.all (fun i => (okB.vars[i]?.map cO.confined).getD false) = true ∧
    okB.opens.any (fun i => (okB.vars[i]?.map cO.confined).getD false) = true ∧
    ok2.opens.any (fun i => (ok2.vars[i]?.map cO.confined).getD false) = false ∧
    okBc.opens.any (fun i => (okBc.vars[i]?.map cO.confined).getD false) = true := by
  decide +kernel

/-- `ok1`, `okB`, `ok2`, `okBc` each compete with a larger rule; `ok2` alone needs a witness, of the
rules and of the clauses. -/
theorem wit :
    (cO.rules.any (fun r => ok1.prio < r.prio) = true ∧ cO.rules.any (fun r => okB.prio < r.prio) = true ∧
      cO.rules.any (fun r => ok2.prio < r.prio) = true ∧ cO.rules.any (fun r => okBc.prio < r.prio) = true) ∧
    ok2.needsWitness cO = true ∧ ok1.needsWitness cO = false ∧ okB.needsWitness cO = false ∧
    okBc.needsWitness cO = false ∧ plain.needsWitness cO = false ∧
    c.rules.all (fun r => !r.needsWitness cO) = true ∧
    cO.fns.all (fun fn => fn.clauses.all fun cl => !cl.needsWitness cO) = true := by
  decide +kernel

/-- **`ok2` is `Witnessed`** at H := 0: `0 ==Int 0` evaluates to `true`. -/
theorem wit2 : ok2.Witnessed cO := by
  refine ⟨[(2, .dv Srt.int (.int 0))], fun j hj s hs => ?_, fun t ht => ?_, .top⟩
  · rw [facts.2.2.1.2.2.2.1] at hj
    cases List.mem_singleton.mp hj
    cases (show some Srt.int = some s from hs)
    exact ⟨_, rfl, sortOf_int 0⟩
  · cases ht
    exact .hook (by decide +kernel) (by decide +kernel) (.cons .var (.cons .dv .nil))
      (fun vs hvs => by cases hvs; rfl) (fun h => by cases h)

/-- `ok4`: X (index 2) by arm A, H (index 3) by arm C only; it competes with `plain` and passes the
competition conjunct by closed conditions (`reqClosed`), its open condition variable H being of the
unconfined sort Int; it needs a witness. -/
theorem facts4 : cO.ruleSorted ok4 = true ∧ cO.rulePlainOpen ok4 = true ∧ ok4.opens = [2, 3] ∧
    ok4.armAB cO 2 = true ∧ ok4.armAB cO 3 = false ∧ ok4.condVars = [3] ∧ ok4.reqOpen = true ∧
    ok4.reqClosed = true ∧ ok4.openCondVars.all (fun i => (ok4.vars[i]?.map cO.confined).getD false) = false ∧
    cO.rules.any (fun r => ok4.prio < r.prio) = true ∧ ok4.needsWitness cO = true ∧
    ok2.reqOpen = true ∧ ok2.openCondVars.all (fun i => (ok2.vars[i]?.map cO.confined).getD false) = false := by
  decide +kernel

/-- **`ok4` is `Witnessed`** at H := 0. -/
theorem wit4 : ok4.Witnessed cO := by
  refine ⟨[(3, .dv Srt.int (.int 0))], fun j hj s hs => ?_, fun t ht => ?_, .top⟩
  · rw [facts4.2.2.2.2.2.1] at hj
    cases List.mem_singleton.mp hj
    cases (show some Srt.int = some s from hs)
    exact ⟨_, rfl, sortOf_int 0⟩
  · cases ht
    exact .hook (by decide +kernel) (by decide +kernel) (.cons .var (.cons .dv .nil))
      (fun vs hvs => by cases hvs; rfl) (fun h => by cases h)

/-- Every rule of `cO` that needs a witness is decided. -/
theorem hwO : ∀ r ∈ cO.rules, r.needsWitness cO = true → r.CondDecided cO := by
  intro r hr hw
  rcases List.mem_append.mp hr with hr' | hr'
  · have := List.all_eq_true.mp wit.2.2.2.2.2.2.1 r hr'
    rw [hw] at this; cases this
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [wit.2.2.1] at hw; cases hw
  · rw [wit.2.2.2.1] at hw; cases hw
  · exact Or.inl wit2
  · rw [wit.2.2.2.2.1] at hw; cases hw
  · rw [wit.2.2.2.2.2.1] at hw; cases hw
  · exact Or.inl wit4

/-- No clause of `cO` needs a witness. -/
theorem hcO : ∀ fn ∈ cO.fns, ∀ cl ∈ fn.clauses, cl.needsWitness cO = true → cl.CondDecided cO := by
  intro fn hfn cl hcl hw
  have := List.all_eq_true.mp (List.all_eq_true.mp wit.2.2.2.2.2.2.2 fn hfn) cl hcl
  rw [hw] at this; cases this

theorem readsO : cO.readsConfined = true := coreO.2.1

theorem m1 : ok1 ∈ cO.rules := List.mem_append_right _ (List.mem_cons_self ..)
theorem mB : okB ∈ cO.rules := List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
theorem m2 : ok2 ∈ cO.rules :=
  List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
theorem mBc : okBc ∈ cO.rules := List.mem_append_right _
  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
theorem m4 : ok4 ∈ cO.rules := List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))

/-- The per-rule lemmas of a successor at values, at each open rule of `cO`: every hypothesis on the
rule, the definition and the witnesses proved. -/
example (hft : FnTerminates cO) {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Faithful.Γc cO) : True := by
  have := @Faithful.rule_step_valuesSSx cO M _ I (Semantics.coreOK_iff_ex.mp coreO.1) hft hI hcO ok1 facts.1.1 facts.1.2.1
    (fun _ => readsO) (fun h => hwO ok1 m1 h)
  have := @Faithful.rule_step_valuesSSx cO M _ I (Semantics.coreOK_iff_ex.mp coreO.1) hft hI hcO okB facts.2.1.1 facts.2.1.2.1
    (fun _ => readsO) (fun h => hwO okB mB h)
  have := @Faithful.rule_step_valuesSSx cO M _ I (Semantics.coreOK_iff_ex.mp coreO.1) hft hI hcO ok2 facts.2.2.1.1 facts.2.2.1.2.1
    (fun _ => readsO) (fun h => hwO ok2 m2 h)
  have := @Faithful.rule_subst_AB cO M _ I coreO.1 hI okB facts.2.1.1 facts.2.1.2.2.1 (fun _ => readsO)
  trivial

/-- The value model at `cO`: each open rule's axiom holds in it (`sat_rule_open`), and its `applies`
pattern is where it applies (`applies_iff_open`). -/
example (hd : FnDet cO) (hs : FnSolves cO) : True := by
  have h := hypModel_of_fn coreO.1 hd hs
  have := Faithful.Model.sat_rule_open h (r := ok1) m1 facts.1.1 facts.1.2.1 (h.ruleFactsEx_of_all (by decide +kernel))
  have := Faithful.Model.sat_rule_open h (r := okB) mB facts.2.1.1 facts.2.1.2.1 (h.ruleFactsEx_of_all (by decide +kernel))
  have := Faithful.Model.sat_rule_open h (r := ok2) m2 facts.2.2.1.1 facts.2.2.1.2.1 (h.ruleFactsEx_of_all (by decide +kernel))
  have := Faithful.Model.sat_rule_open h (r := okBc) mBc facts.2.2.2.1 facts.2.2.2.2 (h.ruleFactsEx_of_all (by decide +kernel))
  have := @Faithful.Model.applies_iff_open cO h okB facts.2.1.1 facts.2.1.2.1
  have := @Faithful.Model.applies_iff_open cO h ok2 facts.2.2.1.1 facts.2.2.1.2.1
  trivial

/-- The rules' open facts at `cO`: `ruleSorted` from `coreOK` and `rulePlainEx` decided, and no rule of `cO` has an existential variable (decided), which with
`rulePlainEx` is `rulePlainOpen`. -/
theorem hopenO : ∀ r ∈ cO.rules, cO.ruleSorted r = true ∧ cO.rulePlainOpen r = true := by
  have hex : ∀ r ∈ cO.rules, r.exs = [] := by decide +kernel
  have hfacts := Semantics.ruleFactsEx_of_coreAll coreO.1 (by decide +kernel)
  exact fun r hr => ⟨(hfacts r hr).1, Semantics.rulePlainOpen_iff_ex.mpr ⟨(hfacts r hr).2, hex r hr⟩⟩

/-- **The pinned theorems at `cO`**, from `coreOK` alone: a definition with rules whose left sides
leave a variable open. -/
example (hf : FnHyp cO) (x y : Config cO) (r : Rule) (σ : Subst) (hs : StepBy cO r σ x y)
    (hd : StepDecided cO x.val) (os : List Outcome)
    (hval : ∀ (y : Config cO) (r : Rule) (σ : Subst), r.opens = [] → StepBy cO r σ x y → .val y.val ∈ os)
    (hfam : ∀ r ∈ cO.rules, r.opens ≠ [] → ∀ σ, Unblocked cO r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ os)
    (σ' : Subst) (hu : Unblocked cO okB σ' x.val) (ys : List GroundTerm)
    (hys : ∀ y : Config cO, (∃ σ'', (∀ i ∈ varOccs okB.lhs, σ''.lookup i = σ'.lookup i) ∧ StepBy cO okB σ'' x y) →
      y.val ∈ ys) : ExactC cO ∧ Consistent cO := by
  have := sound_at cO coreO.1 x y r σ hs (fun r' hr' _ hw _ => hwO r' hr' hw) hcO
  have := @complete_at cO coreO.1 x hd os hval hfam hcO
  have := has_model_choice cO coreO.1 hf (Step cO)
  have := @famOpen_values cO coreO.1 hf x okB mB σ' hu (fun i hi => List.all_eq_true.mp conf.2.1 i hi) ys hys
  exact ⟨exact_hyp cO coreO.1 hf,
    consistent_of cO coreO.1 (fnModel_of_fnHyp coreO.1 hf).1 (fnModel_of_fnHyp coreO.1 hf).2
      (clausePreDecided_of_fnHyp coreO.1 hf)
      (clausePostDecided_of_fnHypCEx (Semantics.coreOK_iff_ex.mp coreO.1) hf) hf.2.2.2.2.2⟩

/-- **`sound_at` at a step by each open rule of `cO`**, one per arm (`ok1` arm A, `okB` arm B, `ok2`
arm C, `ok4` arms A and C with the competition conjunct by closed conditions), and `complete_at`
and `consistent_of` at `cO`: every premise but the step and the functions' hypotheses proved. -/
example (hf : FnHyp cO) (x : Config cO) (hdec : StepDecided cO x.val)
    (y1 yB y2 y4 : Config cO) (σ1 σB σ2 σ4 : Subst)
    (h1 : StepBy cO ok1 σ1 x y1) (hB : StepBy cO okB σB x yB) (h2 : StepBy cO ok2 σ2 x y2)
    (h4 : StepBy cO ok4 σ4 x y4) (os : List Outcome)
    (hval : ∀ (y : Config cO) (r : Rule) (σ : Subst), r.opens = [] → StepBy cO r σ x y → .val y.val ∈ os)
    (hfam : ∀ r ∈ cO.rules, r.opens ≠ [] → ∀ σ, Unblocked cO r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ os) : Consistent cO := by
  have hw : ∀ r : Rule, ∀ r' ∈ cO.rules, r'.prio < r.prio → r'.needsWitness cO = true →
      (∃ σ', PatVal cO σ' r'.lhs x.val) → r'.CondDecided cO := fun _ r' hr' _ hw _ => hwO r' hr' hw
  have := sound_at cO coreO.1 x y1 ok1 σ1 h1 (hw ok1) hcO
  have := sound_at cO coreO.1 x yB okB σB hB (hw okB) hcO
  have := sound_at cO coreO.1 x y2 ok2 σ2 h2 (hw ok2) hcO
  have := sound_at cO coreO.1 x y4 ok4 σ4 h4 (hw ok4) hcO
  have := @complete_at cO coreO.1 x hdec os hval hfam hcO
  exact consistent_of cO coreO.1 (fnModel_of_fnHyp coreO.1 hf).1 (fnModel_of_fnHyp coreO.1 hf).2
      (clausePreDecided_of_fnHyp coreO.1 hf)
      (clausePostDecided_of_fnHypCEx (Semantics.coreOK_iff_ex.mp coreO.1) hf) hf.2.2.2.2.2

/-- info: 'OpenRulesCore.R.coreO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coreO
/-- info: 'OpenRulesCore.R.wit2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wit2

end R

/-! ## Clauses: `cOC` -/

namespace C

definition_of defn from "f2-examples/opencl.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def i (n : Int) : Term := .dv Srt.int (.int n)

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
/-- The text's rule with B:Bool open, held by the `ensures` only. -/
noncomputable def rB : Rule := { r0 with vars := r0.vars ++ [Srt.bool], ens := some (.var 1) }

noncomputable abbrev cOC : Semantics := { c with rules := c.rules ++ [rB] }

/-- `g`'s clauses in the text: `g(_) => 0 [owise]`. -/
noncomputable def gText : List Clause := (c.fns.map (·.clauses)).getD 0 []

/-- `g(X) => 1 requires B` -/
def clB : Clause := { vars := [Srt.int, Srt.bool], pats := [.var 0], req := some (.var 1), rhs := i 1, ens := none }
/-- `g(X) => 1 requires X ==Int 0` -/
def clP : Clause := { vars := [Srt.int], pats := [.var 0], req := some (.app intEq [.var 0, i 0]), rhs := i 1, ens := none }
/-- `g(1) => 1 requires H ==Int 0` -/
def clW : Clause := { vars := [Srt.int], pats := [i 1], req := some (.app intEq [.var 0, i 0]), rhs := i 1, ens := none }

noncomputable def gB : Fn := { label := 389, args := [Srt.int], result := Srt.int, clauses := clB :: gText }
noncomputable def gP : Fn := { label := 389, args := [Srt.int], result := Srt.int, clauses := clP :: gText }
noncomputable def gW : Fn := { label := 389, args := [Srt.int], result := Srt.int, clauses := clW :: gText }

/-- **`cOC` has `coreOK`, reads a confined sort, and its rule `rB` leaves B open**; the clauses'
facts; `clB`'s open condition variable is of a confined sort, `clW`'s is not and needs a witness. -/
theorem coreOC : cOC.coreOK = true ∧ cOC.readsConfined = true ∧ rB.opens = [1] ∧
    (cOC.clauseSortedOpen gB (cOC.fns.map Fn.sig) clB = true ∧ cOC.clausePlainOpen clB = true) ∧
    (cOC.clauseSortedOpen gP (cOC.fns.map Fn.sig) clP = true ∧ cOC.clausePlainOpen clP = true) ∧
    (cOC.clauseSortedOpen gW (cOC.fns.map Fn.sig) clW = true ∧ cOC.clausePlainOpen clW = true) ∧
    clB.openCondVars.any (fun i => (clB.vars[i]?.map cOC.confined).getD false) = true ∧
    clB.needsWitness cOC = false ∧ clP.needsWitness cOC = false ∧
    clP.openCondVars.any (fun i => (clP.vars[i]?.map cOC.confined).getD false) = false ∧
    clW.needsWitness cOC = true ∧
    clW.openCondVars.any (fun i => (clW.vars[i]?.map cOC.confined).getD false) = false := by
  decide_cheap

/-- **`clW` is `Witnessed`** at H := 0: `0 ==Int 0` evaluates to `true`, and by inversion of the
hook to nothing else. -/
theorem witW : clW.Witnessed cOC := by
  refine Clause.witnessed_of_top rfl (σ := [(0, .dv Srt.int (.int 0))]) (fun j _ s hs => ?_) (fun t ht => ?_)
  · cases j with
    | zero => cases (show some Srt.int = some s from hs); exact ⟨_, rfl, sortOf_int 0⟩
    | succ j => cases (show (none : Option Srt) = some s from hs)
  · cases ht
    refine ⟨.hook (by decide +kernel) (by decide +kernel) (.cons .var (.cons .dv .nil))
      (fun vs hvs => by cases hvs; rfl) (fun h => by cases h), fun r hr => ?_⟩
    cases hr with
    | ctor h _ => exact absurd h (by decide +kernel)
    | hook h hhk hts hh hund =>
      cases hts with
      | cons h1 hs1 =>
        cases h1
        cases hs1 with
        | cons h2 hs2 =>
          cases h2
          cases hs2
          have h3 := hh _ rfl
          have h4 : cOC.hookRes intEq [.dv Srt.int (.int 0), .dv Srt.int (.int 0)] =
              some (some (.dv Srt.bool (.bool true))) := by rfl
          exact Option.some.inj (h3.symm.trans h4)
    | param h hhk hp _ _ => exact absurd hhk (by decide +kernel)
    | call h hh _ _ _ _ => exact absurd hh (by decide +kernel)
    | callUndef h hh _ _ _ => exact absurd hh (by decide +kernel)
    | ovl h ho _ => exact absurd ho (by decide +kernel)
    | ovlFn h ho => exact absurd ho (by decide +kernel)

/-- `exclEmptyCl_of` at `clB`, `clP`, `clW` in every model of `Γc cOC`: that `cOC` reads a confined
sort and that `clW` is decided are proved, not assumed. -/
example {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Faithful.Γc cOC) :
    Faithful.ExclEmptyCl cOC I gB clB ∧ Faithful.ExclEmptyCl cOC I gP clP ∧ Faithful.ExclEmptyCl cOC I gW clW :=
  ⟨Faithful.exclEmptyCl_of coreOC.1 hI Faithful.fns_headsOK coreOC.2.2.2.1.1 coreOC.2.2.2.1.2 rfl
      (fun _ => coreOC.2.1) (fun h => by rw [coreOC.2.2.2.2.2.2.2.1] at h; cases h),
   Faithful.exclEmptyCl_of coreOC.1 hI Faithful.fns_headsOK coreOC.2.2.2.2.1.1 coreOC.2.2.2.2.1.2 rfl
      (fun _ => coreOC.2.1) (fun h => by rw [coreOC.2.2.2.2.2.2.2.2.1] at h; cases h),
   Faithful.exclEmptyCl_of coreOC.1 hI Faithful.fns_headsOK coreOC.2.2.2.2.2.1.1 coreOC.2.2.2.2.2.1.2 rfl
      (fun _ => coreOC.2.1) (fun _ => Or.inl witW)⟩

/-- `exclEmptyCl_core` at `clW`, from `Fails` alone. -/
example {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Faithful.Γc cOC)
    {w : GroundTerm} (hw : cOC.sortsOf [w] = some [Srt.int]) (hf : Fails cOC [w] clW) : True := by
  have := @Faithful.exclEmptyCl_core cOC M _ I (by decide +kernel) coreOC.1 (by decide +kernel) hI gW clW _ Faithful.fns_headsOK
    coreOC.2.2.2.2.2.1.1 coreOC.2.2.2.2.2.1.2 rfl (fun _ => coreOC.2.1) (fun _ => Or.inl witW) [w] hw hf
  trivial

/-- info: 'OpenRulesCore.C.witW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms witW

/-! ## An open rule and a clause that needs a witness, in one definition: `cOW`

`cOW` is the text with the rule `rB` (B:Bool open, held by the `ensures` only) and `g`'s clauses
`clW` (H:Int open in closed conditions, `needsWitness`) and the `[owise]` clause. It meets
`coreOK`, and `clW` is `Witnessed` at H := 0, which discharges the pinned statements' hypothesis on
the conditions of the clauses (`hcW`) where a clause needs a witness. -/

noncomputable abbrev cOW : Semantics := { c with rules := c.rules ++ [rB], fns := gW :: c.fns.drop 1 }

theorem shapeOW : cOW.coreOK = true ∧ rB.opens = [1] ∧ clW.needsWitness cOW = true ∧
    clW.opens = [0] ∧ gText.all (fun cl => !cl.needsWitness cOW) = true ∧
    (c.fns.drop 1).all (fun fn => fn.clauses.all fun cl => !cl.needsWitness cOW) = true ∧
    cOW.rules.all (fun r => !r.needsWitness cOW) = true := by
  decide_cheap

/-- The account's owed facts at `cOW`: no rule's `CondDecided`; `clW`'s, the first clause of the first
function, over H (index 0). -/
example : Parse.owedCondDecided cOW = [] ∧ Parse.owedClauseCondDecided cOW = [(0, 0, [0])] := by
  decide +kernel

/-- `clW` is `Witnessed` in `cOW` at H := 0 (as `witW` in `cOC`). -/
theorem witOW : clW.Witnessed cOW := by
  refine Clause.witnessed_of_top rfl (σ := [(0, .dv Srt.int (.int 0))]) (fun j _ s hs => ?_) (fun t ht => ?_)
  · cases j with
    | zero => cases (show some Srt.int = some s from hs); exact ⟨_, rfl, sortOf_int 0⟩
    | succ j => cases (show (none : Option Srt) = some s from hs)
  · cases ht
    refine ⟨.hook (by decide +kernel) (by decide +kernel) (.cons .var (.cons .dv .nil))
      (fun vs hvs => by cases hvs; rfl) (fun h => by cases h), fun r hr => ?_⟩
    cases hr with
    | ctor h _ => exact absurd h (by decide +kernel)
    | hook h hhk hts hh hund =>
      cases hts with
      | cons h1 hs1 =>
        cases h1
        cases hs1 with
        | cons h2 hs2 =>
          cases h2
          cases hs2
          have h3 := hh _ rfl
          have h4 : cOW.hookRes intEq [.dv Srt.int (.int 0), .dv Srt.int (.int 0)] =
              some (some (.dv Srt.bool (.bool true))) := by rfl
          exact Option.some.inj (h3.symm.trans h4)
    | param h hhk hp _ _ => exact absurd hhk (by decide +kernel)
    | call _ hh _ _ _ _ => exact absurd hh (by decide +kernel)
    | callUndef _ hh _ _ _ => exact absurd hh (by decide +kernel)
    | ovl _ ho _ => exact absurd ho (by decide +kernel)
    | ovlFn _ ho => exact absurd ho (by decide +kernel)

/-- The clause that needs a witness, `clW`, is `Witnessed`; no other clause needs one. -/
theorem hcW : ∀ fn ∈ cOW.fns, ∀ cl ∈ fn.clauses, cl.needsWitness cOW = true → cl.CondDecided cOW := by
  intro fn hfn cl hcl hw
  rcases List.mem_cons.mp hfn with rfl | hfn'
  · rcases List.mem_cons.mp hcl with rfl | hcl'
    · exact Or.inl witOW
    · have := List.all_eq_true.mp shapeOW.2.2.2.2.1 cl hcl'
      simp [hw] at this
  · have := List.all_eq_true.mp (List.all_eq_true.mp shapeOW.2.2.2.2.2.1 fn hfn') cl hcl
    simp [hw] at this

/-- No rule of `cOW` needs a witness. -/
theorem hwW {x : Config cOW} (r : Rule) : ∀ r' ∈ cOW.rules, r'.prio < r.prio → r'.needsWitness cOW = true →
    (∃ σ', PatVal cOW σ' r'.lhs x.val) → r'.CondDecided cOW := by
  intro r' hr' _ hw _
  have := List.all_eq_true.mp shapeOW.2.2.2.2.2.2 r' hr'
  simp [hw] at this

/-- `rB`, which leaves B open, is a rule of `cOW`. -/
theorem rB_mem : rB ∈ cOW.rules := List.mem_append_right _ (List.mem_singleton_self _)

/-- **`sound_at` at `cOW`**: at every step, both conclusions, nothing assumed of the conditions. -/
example (x y : Config cOW) (r : Rule) (σ : Subst) (hs : StepBy cOW r σ x y) :
    (Faithful.Γc cOW ⊧ (den cOW x.val ⇒ KoreAML.sNext (Faithful.famEx cOW r σ))) ∧
      (Faithful.Γc cOW ⊧ (den cOW y.val ⇒ Faithful.famEx cOW r σ)) :=
  sound_at cOW shapeOW.1 x y r σ hs (hwW (x := x) r) hcW

/-- **`famEx_closed` at `cOW`.** -/
example {x y : Config cOW} {r : Rule} {σ : Subst} (hs : StepBy cOW r σ x y) (hex : r.exs = []) :
    Faithful.Γc cOW ⊧ (Faithful.famEx cOW r σ ≡ den cOW y.val) :=
  famEx_closed cOW shapeOW.1 hs hex hcW

/-- **`complete_at` at `cOW`**, whose rule `rB` leaves a variable open and whose clause `clW` needs
a witness: the step's closure gives every successor in an outcome of `os`. -/
example (x : Config cOW) (hd : StepDecided cOW x.val) (os : List Outcome)
    (hval : ∀ (y : Config cOW) (r : Rule) (σ : Subst), r.opens = [] → StepBy cOW r σ x y → .val y.val ∈ os)
    (hfam : ∀ r ∈ cOW.rules, r.opens ≠ [] → ∀ σ, Unblocked cOW r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ os) :
    (Faithful.Γc cOW ∪ Faithful.Γstep cOW) ⊧
      (den cOW x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (Outcome.pat cOW)))) :=
  complete_at cOW shapeOW.1 x hd os hval hfam hcW

/-- **`OpenDecided` at `cOW`**: no rule needs a witness, and `clW` is `Witnessed`. -/
theorem odOW : OpenDecided cOW :=
  ⟨fun r hr hw => absurd hw (by
      have := List.all_eq_true.mp shapeOW.2.2.2.2.2.2 r hr
      simpa using this),
   hcW⟩

/-- At `cOW` the deciders name one fact, `clW`'s match independence (`matchObligationsL`): its
open H could give two matches. No parameter is open, and `rightValued` holds. -/
theorem factsOW : cOW.rightValued = true ∧ cOW.rankObligations [] ++ cOW.decObligationsL = [] ∧
    cOW.totalObligationsRP [] [] = [] ∧ cOW.agreeObligationsI = [] ∧ cOW.matchObligationsL = [(389, 0)] ∧
    cOW.params.all (fun k => !k.raw) = true := by
  decide +kernel

/-- **`clW` is match independent**: its right side is the literal `1` under every match. -/
theorem miW : MatchIndependent cOW clW :=
  (matchIndependent_iff_noExs rfl).mpr <| Coherent.of_rhs rfl rfl fun _ _ _ _ _ _ _ _ => .inr fun r r' h h' => by
    change EvalTerm _ _ (.dv Srt.int (.int 1)) _ at h h'
    cases h; cases h'; rfl

/-- **`FnFacts cOW`**: the one named fact by `miW`. -/
theorem factsFOW : FnFacts cOW [] [] :=
  ⟨fun f hf => (by rw [factsOW.2.1] at hf; cases hf),
   fun f hf => (by rw [factsOW.2.2.1] at hf; cases hf),
   fun f hf => (by rw [factsOW.2.2.2.1] at hf; cases hf),
   fun p hp fn hfn cl hcl => (by
     rw [factsOW.2.2.2.2.1] at hp
     cases List.mem_singleton.mp hp
     cases (show some gW = some fn from (rfl : cOW.lookupFn 389 = some gW).symm.trans hfn)
     cases (show some clW = some cl from (rfl : gW.clauses[0]? = some clW).symm.trans hcl)
     exact miW),
   openLaws_of_plain fun k hk => by simpa using List.all_eq_true.mp factsOW.2.2.2.2.2 k hk⟩

/-- **`FnHyp cOW`**, from `FnFacts`, `odOW` and `fnHyp_of_fnObligations`. -/
theorem fnHypOW : FnHyp cOW :=
  fnHyp_of_fnObligations shapeOW.1 (Semantics.rightHeld_of_valued factsOW.1) ParamsTotal.nil
    (factsFOW.obligations odOW)

/-- **`StepDecided` at every configuration of `cOW`, `FnDet`, `FnSolves` and `Consistent`**, from
`fnHypOW` (`stepDecided_of_fnHyp`, `fnModel_of_fnHyp`, `consistent_of`). -/
theorem decidedOW (x : Config cOW) : StepDecided cOW x.val := stepDecided_of_fnHyp shapeOW.1 fnHypOW x
theorem fnModelOW : FnDet cOW ∧ FnSolves cOW := fnModel_of_fnHyp shapeOW.1 fnHypOW
theorem consOW : Consistent cOW :=
  consistent_of cOW shapeOW.1 fnModelOW.1 fnModelOW.2 (clausePreDecided_of_fnHyp shapeOW.1 fnHypOW)
    (clausePostDecided_of_fnHypCEx (Semantics.coreOK_iff_ex.mp shapeOW.1) fnHypOW)
    (openLaws_of_plain (by decide +kernel))

/-- `complete_at` at `cOW` with `StepDecided` proved: only the outcomes `hval`, `hfam` are taken. -/
example (x : Config cOW) (os : List Outcome)
    (hval : ∀ (y : Config cOW) (r : Rule) (σ : Subst), r.opens = [] → StepBy cOW r σ x y → .val y.val ∈ os)
    (hfam : ∀ r ∈ cOW.rules, r.opens ≠ [] → ∀ σ, Unblocked cOW r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ os) :
    (Faithful.Γc cOW ∪ Faithful.Γstep cOW) ⊧
      (den cOW x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (Outcome.pat cOW)))) :=
  complete_at cOW shapeOW.1 x (decidedOW x) os hval hfam hcW

/-- **`exclEmptyCl_core` does not apply at `cOW`**: its `hbc` asks every clause to bind its
variables in its patterns, and `clW`'s pattern `1` does not bind H. -/
theorem not_hbcOW : ¬ ∀ fn ∈ cOW.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true :=
  fun h => absurd (h gW (List.mem_cons_self ..) clW (List.mem_cons_self ..)) (by decide +kernel)

/-- **`exclEmptyCl_of` at `clW`, a clause of `cOW`.** -/
example {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Faithful.Γc cOW) :
    Faithful.ExclEmptyCl cOW I gW clW :=
  Faithful.exclEmptyCl_of shapeOW.1 hI Faithful.fns_headsOK (by decide +kernel) (by decide +kernel) rfl
    (fun _ => by decide +kernel) (fun _ => Or.inl witOW)

/-- info: 'OpenRulesCore.C.fnHypOW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnHypOW
/-- info: 'OpenRulesCore.C.consOW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consOW

end C

end OpenRulesCore

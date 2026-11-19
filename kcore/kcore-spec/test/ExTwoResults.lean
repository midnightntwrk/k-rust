/-
  EX's clauses where the two instances differ: a function of no argument, declared `total`, with
  the clauses `Parse.exClauses` writes for the alternatives `true` and `false` with no condition
  and the body `B` (`clauses_eq`), the reading of `f() => #Exists B:Bool. B` (f `total`), built by
  hand:
    `pre := ⌈true⌉`, `rhs := true`; `pre := ⌈false⌉`, `rhs := false`; and
    `pre := ¬∃B:Bool. ⌈B⌉`, `rhs := true`, `ens := false`,
  all of priority 50. Beside it one rule reads f: `<k> K </k> <counter> N </counter> =>
  <k> K </k> <counter> 0 </counter> requires f()`. Run from the package root:
  `lake env lean -j1 test/ExTwoResults.lean`. Kernel-checked.

  - `coreOK` holds (`coreOK_now`): `clausesPlain` admits the clauses' predicates, none of them
    `\top`; `ok`, which asks every predicate `\top`, refuses them (`ok_now`).
    The last clause's predicate has a binder, so the definition reads a confined sort
    (`readsConfined_now`) and `Γc` holds `boolClosed`.
  - `Eval` has both results: `f()` is `true` by the first clause and `false` by the second
    (`eval_true`, `eval_false`): `Eval.clause` reads no other clause of the same priority. So
    `FnDet` is false (`not_fnDet`), and `FnHyp` with it.
  - The statements at `coreOK` alone hold at this semantics: `sound_at` and `famEx_closed` at the
    rule's step from the counter 1 to the counter 0 (`sound_x1`, `famEx_x1`), which `requires f()`
    takes by the result `true`, and `complete_at` at every configuration (`complete_any`); likewise
    their `coreOKEx` siblings (`sound_x1_ce`, `famEx_x1_ce`, `complete_any_ce`).
  - `Γc` has no model (`no_model`, `not_consistent`): in a model each result is what `f()` denotes
    (`eval_den4_coreCl`), so the elements of `true` and of `false` would be one, against
    `NodeFacts.apart`. So the statements above hold here because there is no model to speak of.

  The text `f() => #Exists B:Bool. B` with f `total` has no model either, by its own argument: f's
  functional sentence makes `f()` one element, and the sentence makes it every element of Bool, of
  which `true` and `false` are two distinct ones (the text's Bool domain values). An account of a
  text of this shape should say, as the overload note says for an overloading function, that the
  text has no model where the instances differ.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.ExTwoResults
open KCore GroundTerm

/-! ## The semantics -/

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def kcS : Sym := nRegSyms + 2
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨kcS, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def fS : Sym := nRegSyms + 4
def litT (b : Bool) : Term := .dv Srt.bool (.bool b)

def p1 : Cond := .ceil Srt.bool (litT true)
def p2 : Cond := .ceil Srt.bool (litT false)
def cl1 : Clause := ⟨[], [], none, litT true, none, 50, false, [], p1, .top⟩
def cl2 : Clause := ⟨[], [], none, litT false, none, 50, false, [], p2, .top⟩
def cl3 : Clause := ⟨[], [], none, litT true, some (litT false), 50, false, [], .not (.ex Srt.bool (.ceil Srt.bool (.var 0))), .top⟩

/-- f, declared `total`. -/
def fFn : Fn := ⟨fS, [], Srt.bool, [cl1, cl2, cl3], true⟩

/-- The clauses are `exClauses` over the alternatives `true` and `false` with no condition, and the
body B (the variable at index 0) with no condition. -/
theorem clauses_eq : fFn.clauses =
    Parse.exClauses Srt.bool [] [] none 50 false [(litT true, []), (litT false, [])] [(.var 0, [])] :=
  rfl

/-- `<k> K </k> <counter> N </counter> => <k> K </k> <counter> 0 </counter> requires f()` -/
def r0 : Rule :=
  { vars := [Srt.k, Srt.int], lhs := .app topLabel [.app kcS [.var 0], .app counterLabel [.var 1]],
    req := some (.app fS []), rhs := .app topLabel [.app kcS [.var 0], .app counterLabel [.dv Srt.int (.int 0)]],
    ens := none, prio := 50 }

def c : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [fFn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [r0] }

/-! ## `coreOK` -/

/-- `clausesPlain` admits f's clauses with their predicates. -/
theorem clausesPlain_now : c.clausesPlain = true := by decide +kernel

/-- **`coreOK` holds.** -/
theorem coreOK_now : c.coreOK = true := by
  unfold Semantics.coreOK Semantics.sortedOK; decide_cheap

/-- f's clauses have predicates that are not `\top`, which `ok` refuses. -/
theorem clausesPreTop_now : c.clausesPreTop = false := by decide +kernel
theorem ok_now : c.ok = false := by
  cases h : c.ok
  · rfl
  · exact absurd (Semantics.preTop_of_okAll (Semantics.okAll_of_ok h)) (by rw [clausesPreTop_now]; decide)

/-- The last clause's predicate has a binder. -/
theorem readsConfined_now : c.readsConfined = true := by decide +kernel

theorem coreOKEx_now : c.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap

/-- No rule and no clause needs a witness. -/
theorem noWitR : ∀ r ∈ c.rules, r.needsWitness c = false := by decide +kernel
theorem noWitCl : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = false := by decide +kernel

theorem noWit : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c :=
  fun fn hfn cl hcl hw => absurd hw (by rw [noWitCl fn hfn cl hcl]; decide)

theorem mem_rules {r : Rule} (h : r ∈ c.rules) : r = r0 := by simpa [c] using h

/-! ## The two results -/

theorem lookupF : c.lookupFn fS = some fFn := by rw [Semantics.lookupFn_eq]; rfl

theorem flagsF : c.isCtor fS = false ∧ isHook fS = false ∧ c.isParam fS = false := by decide +kernel

/-- No clause of f has a smaller priority than another. -/
theorem prio_none {d : Semantics} {cl : Clause} (hcl : cl ∈ fFn.clauses) :
    ∀ cl' ∈ fFn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails d [] cl' := by
  intro cl' hcl' _ hlt
  simp only [fFn, List.mem_cons, List.not_mem_nil, or_false] at hcl hcl'
  rcases hcl with rfl | rfl | rfl <;> rcases hcl' with rfl | rfl | rfl <;> exact absurd hlt (by decide)

theorem nil_sorted : c.WellSorted [] [] := fun i s hs => by simp at hs

/-- The clause of the literal b, of the two first, gives b. -/
theorem eval_lit {b : Bool} {cl : Clause} (hcl : cl ∈ fFn.clauses) (hrhs : cl.rhs = litT b) (hens : cl.ens = none)
    (hvars : cl.vars = []) (hpats : cl.pats = []) (hreq : cl.req = none) (hex : cl.exs = []) (hpost : cl.post = .top)
    (hpre : cl.pre = .ceil Srt.bool (litT b)) : Eval c fS [] (some (bool b)) := by
  refine .clause lookupF hcl (by rw [hvars]; exact nil_sorted) (by rw [hpats]; exact .nil)
    (fun t ht => by rw [hreq] at ht; cases ht) ?_ (prio_none hcl) hex (by rw [hrhs]; exact .dv)
    (fun t ht => by rw [hens] at ht; cases ht) (by rw [hpost]; exact .top)
  rw [hpre]
  exact Holds.ceil (r := some (bool b)) .dv

/-- **`f()` is `true`**, by the first clause. -/
theorem eval_true : Eval c fS [] (some (bool true)) :=
  eval_lit (cl := cl1) (by simp [fFn]) rfl rfl rfl rfl rfl rfl rfl rfl

/-- **`f()` is `false`**, by the second clause. -/
theorem eval_false : Eval c fS [] (some (bool false)) :=
  eval_lit (cl := cl2) (by simp [fFn]) rfl rfl rfl rfl rfl rfl rfl rfl

/-- **`FnDet` is false.** -/
theorem not_fnDet : ¬ FnDet c := fun h => by
  have := h fS [] _ _ eval_true eval_false
  simp [bool] at this

theorem not_fnHyp : ¬ FnHyp c := fun h => not_fnDet (fnModel_of_fnHyp coreOK_now h).1

/-! ## The rule's step from the counter 1 to the counter 0 -/

def cfgV (k n : GroundTerm) : GroundTerm := .ctor topLabel [.ctor kcS [k], .ctor counterLabel [n]]

theorem ctorsV : c.isCtor topLabel = true ∧ c.isCtor counterLabel = true ∧ c.isCtor kcS = true := by
  decide +kernel

/-- `<k> . </k> <counter> 1 </counter>` -/
def x1 : Config c := ⟨cfgV (.ctor dotk []) (.dv Srt.int (.int 1)), by decide +kernel⟩
/-- `<k> . </k> <counter> 0 </counter>` -/
def y0 : Config c := ⟨cfgV (.ctor dotk []) (.dv Srt.int (.int 0)), by decide +kernel⟩

def σX : Subst := [(0, .ctor dotk []), (1, .dv Srt.int (.int 1))]

theorem sorts_σX : c.sortOf (.ctor dotk []) = some Srt.k ∧ c.sortOf (.dv Srt.int (.int 1)) = some Srt.int := by
  decide +kernel

/-- `f()` evaluates to `true` under any σ. -/
theorem termF (σ : Subst) : EvalTerm c σ (.app fS []) (some (bool true)) :=
  .call flagsF.1 flagsF.2.1 .nil rfl eval_true flagsF.2.2

/-- **The rule's step** from the counter 1 to the counter 0, its `requires f()` by the result `true`. -/
theorem stepX : StepBy c r0 σX x1 y0 :=
  { mem := List.mem_singleton_self _
    hσ := fun i s hs => by
      match i, hs with
      | 0, hs => cases (show some Srt.k = some s from hs); exact ⟨_, rfl, sorts_σX.1⟩
      | 1, hs => cases (show some Srt.int = some s from hs); exact ⟨_, rfl, sorts_σX.2⟩
      | _ + 2, hs => cases (show (none : Option Srt) = some s from hs)
    hmatch := .ctor ctorsV.1 (.cons (.ctor ctorsV.2.2 (.cons (.var rfl) .nil))
      (.cons (.ctor ctorsV.2.1 (.cons (.var rfl) .nil)) .nil))
    hreq := fun t ht => by cases ht; exact termF σX
    hpre := .top
    heval := .ctor ctorsV.1 (.cons (.ctor ctorsV.2.2 (.cons (.var (i := 0)) .nil))
      (.cons (.ctor ctorsV.2.1 (.cons .dv .nil)) .nil))
    hens := fun t ht => nomatch ht
    hpost := .top
    hprio := fun r' hr' hlt => by
      obtain rfl := mem_rules hr'
      exact absurd hlt (Nat.lt_irrefl _) }

/-- Every configuration's step is decided: `f()` has a value and the right side evaluates. -/
theorem stepDecided (x : GroundTerm) : StepDecided c x := by
  intro r hr _
  obtain rfl := mem_rules hr
  exact ⟨fun σ _ _ => ⟨fun t ht => by cases ht; exact ⟨_, termF σ⟩, true, Holds.top⟩,
    fun σ _ _ _ _ => ⟨⟨_, .ctor ctorsV.1 (.cons (.ctor ctorsV.2.2 (.cons .var .nil))
      (.cons (.ctor ctorsV.2.1 (.cons .dv .nil)) .nil))⟩, (fun e he => nomatch he), true, Holds.top⟩⟩

/-! ## The statements at `coreOK` -/

/-- No rule of `c` has a smaller priority than another. -/
theorem hw (r : Rule) (hr : r ∈ c.rules) (x : Config c) : ∀ r' ∈ c.rules, r'.prio < r.prio →
    r'.needsWitness c = true → (∃ σ', PatVal c σ' r'.lhs x.val) → r'.CondDecided c := by
  intro r' hr' hlt
  obtain rfl := mem_rules hr; obtain rfl := mem_rules hr'
  exact absurd hlt (Nat.lt_irrefl _)

/-- **`sound_at` at the rule's step from the counter 1 to the counter 0.** -/
theorem sound_x1 :
    (Faithful.Γc c ⊧ (den c x1.val ⇒ KoreAML.sNext (Faithful.famEx c r0 σX))) ∧
      (Faithful.Γc c ⊧ (den c y0.val ⇒ Faithful.famEx c r0 σX)) :=
  sound_at c coreOK_now x1 y0 r0 σX stepX (hw r0 stepX.mem x1) noWit

/-- **`famEx_closed` at that step.** -/
theorem famEx_x1 : Faithful.Γc c ⊧ (Faithful.famEx c r0 σX ≡ den c y0.val) :=
  famEx_closed c coreOK_now stepX rfl noWit

/-- **`complete_at` at every configuration**, for any list of outcomes holding the successors
(the rule binds every variable of its left side, so no family is asked for). -/
theorem complete_any (x : Config c) (os : List Outcome)
    (hval : ∀ (y : Config c) (r : Rule) (σ : Subst), r.opens = [] → StepBy c r σ x y → .val y.val ∈ os) :
    (Faithful.Γc c ∪ Faithful.Γstep c) ⊧
      (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (Outcome.pat c)))) :=
  complete_at c coreOK_now x (stepDecided x.val) os hval
    (fun r hr hne => absurd (by obtain rfl := mem_rules hr; decide) hne) noWit

/-- **`sound_at_ce` at that step.** -/
theorem sound_x1_ce :
    (Faithful.Γc c ⊧ (den c x1.val ⇒ KoreAML.sNext (Faithful.famEx c r0 σX))) ∧
      (Faithful.Γc c ⊧ (den c y0.val ⇒ Faithful.famEx c r0 σX)) :=
  sound_at_ce c coreOKEx_now x1 y0 r0 σX stepX
    (fun r' hr' hlt => by obtain rfl := mem_rules hr'; exact absurd hlt (Nat.lt_irrefl _)) noWit

/-- **`famEx_closed_ce` at that step.** -/
theorem famEx_x1_ce : Faithful.Γc c ⊧ (Faithful.famEx c r0 σX ≡ den c y0.val) :=
  famEx_closed_ce c coreOKEx_now stepX rfl noWit

/-- **`complete_at_ce` at every configuration.** -/
theorem complete_any_ce (x : Config c) (os : List Outcome)
    (hval : ∀ (y : Config c) (r : Rule) (σ : Subst), r.opens = [] → StepBy c r σ x y → .val y.val ∈ os) :
    (Faithful.Γc c ∪ Faithful.Γstep c) ⊧
      (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (Outcome.pat c)))) :=
  complete_at_ce c coreOKEx_now x (stepDecided x.val) os hval
    (fun r hr hne => absurd (by obtain rfl := mem_rules hr; decide) hne) noWit

/-! ## `Γc` has no model -/

section NoModel

open ML Faithful

/-- **`Γc` has no model**: `f()` would denote the element of `true`, its result by the first clause,
and the element of `false`, its result by the second, which are apart. -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γc c) := by
  intro M _ I hIc
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core coreOK_now
  haveI : OvlOK c := hno
  have F := HoldsShape.nodeFacts_of_core coreOK_now hIc
  have hden := fun (r : Option GroundTerm) (hev : Eval c fS [] r) (e : Valuation M) (m : M) =>
    eval_den4_coreCl hIc (Semantics.sortedOKCl_of_sortedOK_noExs hok (Semantics.fnsNoExs_of_all (by decide +kernel))) hsr (Semantics.coreOK_parts coreOK_now).2.1 hph
      noWit (HoldsShape.preReadAll_of_core coreOK_now hIc) hev lookupF (by decide +kernel) e m
  let e : Valuation M := ⟨fun _ => default, fun _ _ => False⟩
  obtain ⟨a, ha, -⟩ := F.val (rmS_sortOf_bool c true) [] e
  have h1 := (hden _ eval_true e a).mpr ((ha a).mpr rfl)
  have h2 := (hden _ eval_false e a).mp h1
  have := F.apart (rmS_sortOf_bool c true) (rmS_sortOf_bool c false) e a ((ha a).mpr rfl) h2
  simp [bool] at this

/-- **Not `Consistent`**: `Γc` is part of `Γc ∪ Γstep`. -/
theorem not_consistent : ¬ Consistent c := fun ⟨M, hM, I, hI⟩ =>
  no_model M hM I (fun φ hφ => hI φ (Or.inl hφ))

end NoModel

end KCore.ExTwoResults

#check @KCore.ExTwoResults.eval_true
#check @KCore.ExTwoResults.eval_false
#check @KCore.ExTwoResults.not_fnDet
#check @KCore.ExTwoResults.sound_x1
#check @KCore.ExTwoResults.famEx_x1
#check @KCore.ExTwoResults.complete_any
#check @KCore.ExTwoResults.no_model
/-- info: 'KCore.ExTwoResults.coreOK_now' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ExTwoResults.coreOK_now
/-- info: 'KCore.ExTwoResults.not_fnDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ExTwoResults.not_fnDet
/-- info: 'KCore.ExTwoResults.sound_x1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ExTwoResults.sound_x1
/-- info: 'KCore.ExTwoResults.famEx_x1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ExTwoResults.famEx_x1
/-- info: 'KCore.ExTwoResults.complete_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ExTwoResults.complete_any
/-- info: 'KCore.ExTwoResults.no_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ExTwoResults.no_model

/-
  The fixture e2-clause-rhs-empty: `rule f() => g(Y:Empty) [unboundVariables(Y)]` (`syntax Empty`,
  no production; `T ::= g(Empty)`, `T ::= f() [function]`). The text is
  `f2-examples/rhsempty.kompile.kore`; its equation of `f` is `f() = g(Y)` with Y free, so universal
  over Empty. Run from the package root: `lake env lean -j1 test/TieClauseRhsEmptyC.lean`.

  The text determines no value of `f()` (C7 form (c)): the reading's theory with the step's closure
  entails neither that `f()` has no element nor that it is a value of its sort. Both by one model,
  the model of `KCore.EmptyInh` in which Empty holds an element `e` (`cP := EmptyInh.plus c 33`, c
  with one open generator of sort Empty, a constant): it is a model of c's theory (`model`), and in
  it the equation at `Y = e` makes `f()` the element of `g(e)` (`f_is_ge`), which is not empty and
  is no value of c, since `g(e)` and a value of T are distinct values of T in `cP`
  (`values_apart`). In the value model of c, where Empty is empty, the equation is vacuous and
  `f()` has no result (`test/RightOnly.lean`, `fE_none`, for the hand-built twin).

  The hypotheses of `EmptyInh.premises_sub` and `FnHyp cP` are those of
  `test/ModelEmptyInhabited.lean` (namespace `EmptyInhFixtures.Rhs`), restated here; they hold at
  the interpretation the parsed data carries, `HookParams.none`, which is the H the statements'
  negations are witnessed at.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieClauseRhsEmptyC

open KCore ML Faithful KoreAML EmptyInh

definition_of defn from "f2-examples/rhsempty.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable abbrev cP : Semantics := plus c 33

def fS : Sym := 387
def gS : Sym := 386

theorem names : c.symName fS = "Lblf" ∧ c.symName gS = "Lblg" ∧ c.sortName 33 = "Empty" ∧
    eSym c = 388 := by
  decide +kernel

/-- The parsed data's interpretation is `HookParams.none`. -/
theorem cH_none : cH HookParams.none = c := rfl

/-! ## The second model (the hypotheses of `EmptyInh.premises_sub` and `FnHyp cP`) -/

theorem facts : c.ovls = [] ∧ c.params = [] ∧ c.ctorSigs.all (·.name != eSym c) = true ∧ c.gens 33 = [] ∧
    (c.readsConfined = true → cP.readsConfined = true) ∧ (c.litSort Srt.bool = true → cP.litSort Srt.bool = true) := by
  decide +kernel

theorem hooksNone : ∀ f vs, c.hooks.app f vs = none := fun _ _ => rfl

theorem empty : c.ctorSigs.all (·.result != 33) = true ∧ c.subsorts.all (fun p => p.2 != 33) = true ∧
    c.collOf 33 = none ∧ c.lib.carriers.all (·.1 != 33) = true ∧
    ((33 : Srt) != Srt.int && (33 : Srt) != Srt.bool && (33 : Srt) != Srt.kconfigVar && (33 : Srt) != Srt.string &&
      (33 : Srt) != Srt.bytes && (33 : Srt) != Srt.float && !c.lib.tokenSorts.contains 33 &&
      !c.lib.byteSorts.contains 33) = true := by
  decide +kernel

theorem fresh : ∀ k ∈ c.ctorSigs, k.name ≠ eSym c := fun k hk => by
  simpa using List.all_eq_true.mp facts.2.2.1 k hk

theorem freshP : ∀ k ∈ c.params, k.sig.name ≠ eSym c := fun k hk => by
  rw [facts.2.1] at hk; cases hk

theorem noRaw : ∀ k ∈ c.params, k.raw = false := fun k hk => by rw [facts.2.1] at hk; cases hk

theorem sortOf_e : cP.sortOf (eVal c) = some 33 :=
  EmptyInh.sortOf_e facts.1 fresh freshP (keepsRaw_of_none hooksNone)

theorem value_eq {v : GroundTerm} (h : cP.sortOf v = some 33) : v = eVal c :=
  value_E_eq empty.1 facts.1 noRaw empty.2.1 empty.2.2.1 empty.2.2.2.1 empty.2.2.2.2 h

noncomputable def fF : Fn := c.fns[0]'(by decide +kernel)
noncomputable def clY : Clause := fF.clauses[0]'(by decide +kernel)

theorem fF_mem : fF ∈ c.fns := List.getElem_mem _

/-- `f() => g(Y:Empty)`, alone; `g : Empty → T` is a constructor. -/
theorem shape : c.fns.length = 1 ∧ fF.label = fS ∧ fF.args = [] ∧ fF.clauses.length = 1 ∧
    clY.vars = [33] ∧ clY.leftVars = [] ∧ clY.exs = [] ∧ c.isCtor gS = true ∧
    lookupSig c.ctorSigs gS = some ⟨gS, [33], fF.result⟩ := by
  decide +kernel

theorem clY_pats : clY.pats = [] := by rfl
theorem clY_req : clY.req = none := by rfl
theorem clY_ens : clY.ens = none := by rfl
theorem clY_rhs : clY.rhs = .app gS [.var 0] := by rfl
theorem clY_pre : clY.pre = .top := by rfl

theorem fns_eq : c.fns = [fF] := by
  apply List.ext_getElem (by rw [shape.1]; rfl)
  intro i h1 _
  have : i < 1 := shape.1 ▸ h1
  match i, this with
  | 0, _ => rfl

theorem clauses_eq : fF.clauses = [clY] := by
  apply List.ext_getElem (by rw [shape.2.2.2.1]; rfl)
  intro i h1 _
  have : i < 1 := shape.2.2.2.1 ▸ h1
  match i, this with
  | 0, _ => rfl

theorem noFail : ∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ cl ∈ fn.clauses, ¬ Fails c vs cl := by
  intro fn hfn vs hvs
  rw [fns_eq, List.mem_singleton] at hfn
  subst hfn
  rw [shape.2.2.1] at hvs
  rw [sortsOf_nil_of hvs, clauses_eq]
  exact ⟨clY, List.mem_singleton_self _, not_fails_nil clY_pats shape.2.2.2.2.2.1 clY_req clY_pre⟩

theorem sub : ∀ φ, φ ∈ Γc c ∪ Γstep c → φ ∈ Γc cP ∪ Γstep cP :=
  premises_sub facts.1 fresh facts.2.2.2.1
    (fun k hk => by rw [facts.2.1] at hk; cases hk)
    (fun k _ vs _ _ _ => fallback_plus_of_none hooksNone k.name vs)
    (hfails_of_noFail noFail) facts.2.2.2.2.1 facts.2.2.2.2.2

theorem namedP : cP.coreOK = true ∧ cP.heldObligations = [fS] ∧
    cP.rankObligations [fS] ++ cP.decObligationsL = [] ∧ cP.totalObligationsRP [fS] [] = [] ∧
    cP.agreeObligationsI = [] ∧ cP.matchObligationsL = [(fS, 0)] ∧ cP.owedRules = [] ∧
    cP.owedClauses = [] := by
  decide_cheap

theorem coreP : cP.coreOK = true := namedP.1

theorem lookupF : cP.lookupFn fS = some fF :=
  shape.2.1 ▸ lookupFn_of_core coreP (show fF ∈ cP.fns from fF_mem)

theorem lookupF_eq {fn : Fn} (h : cP.lookupFn fS = some fn) : fn = fF :=
  Option.some.inj (h.symm.trans lookupF)

theorem held : ∀ f ∈ cP.heldObligations, HeldOwed cP f := by
  intro f hf fn hfn
  rw [namedP.2.1, List.mem_singleton] at hf
  subst hf
  have e := lookupF_eq hfn
  subst e
  refine .inl fun cl hcl i s hi => .inr ?_
  rw [clauses_eq, List.mem_singleton] at hcl
  subst hcl
  rw [shape.2.2.2.2.1] at hi
  cases i with
  | zero => cases hi; exact ⟨eVal c, sortOf_e⟩
  | succ i => simp at hi

theorem matchY : MatchIndependent cP clY := by
  obtain ⟨-, -, -, -, hv, -, hx, -⟩ := shape
  have he := clY_ens
  have hrhs := clY_rhs
  refine (matchIndependent_iff_noExs hx).mpr fun vs σ σ' ha ha' _ _ _ _ _ => .inl
    ⟨hx, hx, rfl, rfl, fun i hi => ?_, fun t ht => by rw [he] at ht; cases ht⟩
  rw [hrhs] at hi
  simp [varOccs, varOccsList] at hi
  subst hi
  have h0 : (0 : Nat) ∈ clY.univ := by simp [Clause.univ, hv, hx]
  obtain ⟨v, hv1, hv2⟩ := ha.1 0 h0 33 (by rw [hv]; rfl)
  obtain ⟨w, hw1, hw2⟩ := ha'.1 0 h0 33 (by rw [hv]; rfl)
  rw [hv1, hw1, value_eq hv2, value_eq hw2]

theorem oblP : FnObligations cP [fS] [] := by
  obtain ⟨-, -, hterm, htot, hagr, hmat, howR, howC⟩ := namedP
  refine ⟨fun f hf => (by rw [hterm] at hf; cases hf), fun f hf => (by rw [htot] at hf; cases hf),
    fun f hf => (by rw [hagr] at hf; cases hf), fun p hp fn hfn cl hcl => ?_,
    ⟨openRules_of_owed (by rw [howR]; intro i hi; cases hi),
     openClauses_of_owed (by rw [howC]; intro p hp; cases hp)⟩, ?_⟩
  · rw [hmat, List.mem_singleton] at hp
    subst hp
    have e := lookupF_eq hfn
    subst e
    rw [clauses_eq] at hcl
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hcl
    subst hcl
    exact matchY
  · intro k hk _
    have hk' : k ∈ c.params ++ [eParam c 33] := hk
    rw [facts.2.1, List.nil_append, List.mem_singleton] at hk'
    subst hk'
    exact ⟨fun h => by simp [eParam] at h, fun h => by simp [eParam] at h⟩

theorem fnHypP : FnHyp cP := fnHyp_of_fnObligationsN coreP held ParamsTotal.nil oblP

theorem model : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc cP ∪ Γstep cP)) ∧ (I ⊧ᴵP (Γc c ∪ Γstep c)) :=
  model_exists sub coreP fnHypP

/-! ## `f()` in the second model: the element of `g(e)` -/

/-- The value `g(e)` of `cP`. -/
noncomputable def ge : GroundTerm := .ctor gS [eVal c]

theorem ge_sort : cP.sortOf ge = some fF.result :=
  sortOf_ctor_intro ⟨_, shape.2.2.2.2.2.2.2.2, sortsOf_cons.mpr ⟨_, _, sortOf_e, sortsOf_nil, rfl⟩, rfl⟩

/-- `g(e)` is no value of c: Empty has none there. -/
theorem ge_not_c : c.sortOf ge = none := by decide +kernel

/-- `Y ↦ e`. -/
noncomputable def σe : Subst := [(0, eVal c)]

theorem ws_e : cP.WellSorted clY.vars σe := fun i s hs => by
  rw [shape.2.2.2.2.1] at hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨_, rfl, sortOf_e⟩
  | succ i => simp at hs

theorem patval : PatVal cP σe clY.rhs ge := by
  rw [clY_rhs]
  exact .ctor shape.2.2.2.2.2.2.2.1 (.cons (.var rfl) .nil)

theorem lowY : lowerClauses fF clY = [] := List.isEmpty_iff.mp (by decide +kernel)

theorem rhsv : ∀ i ∈ varOccs clY.rhs, i < clY.vars.length := by
  rw [clY_rhs, shape.2.2.2.2.1]; simp [varOccs, varOccsList]

theorem rhs_plainP : plainPat cP clY.rhs = true := by decide +kernel
theorem rhs_sortP : sortOfTerm cP.patCtxAll clY.vars clY.rhs = some fF.result := by decide +kernel
theorem pats_sortsP : sortsOfTerms cP.patCtxAll clY.vars clY.pats = some fF.args := by
  rw [clY_pats, shape.2.2.1]; rfl

theorem occ : ∀ i < clY.vars.length, i ∈ varOccsList clY.pats ++ clY.condVars ++ varOccs clY.rhs ++
    (clY.ens.map varOccs).getD [] := by
  intro i hi
  rw [shape.2.2.2.2.1] at hi
  have : i = 0 := by simpa using hi
  subst this
  rw [clY_rhs]
  simp [varOccs, varOccsList]

/-- **The equation at `Y = e`**: in a model of `cP`'s Γ, `f()` is what `g(e)` denotes. -/
theorem f_is_ge {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hΓ : I ⊧ᴵP Γ cP)
    (e0 : Valuation M) (m : M) :
    (TiePair.app c fS []).interpret I e0 m ↔ (den c ge).interpret I e0 m := by
  obtain ⟨hsok, hsr', hnn, -, -, -, -, -, hno⟩ := hypSound_of_core coreP
  haveI : OvlOK cP := hno
  have htr := (sortCtx_of_all hsok hsr' (OvlOK.ovlCase hno)).trans
  have hfnm := (lookupFn_spec lookupF).1
  have ihrhs : ∀ (tbl : VarTable) (e : Valuation M), Agrees cP I tbl (canonVars cP clY.vars) σe e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight cP fF clY)).interpret I e m ↔ Res cP I e (some ge) m :=
    fun tbl e hag => right_iff hΓ hnn hfnm (fun v hv => by cases hv; exact ge_sort)
      (fun m => (patVal_den hΓ hnn.1 htr ws_e (canonVars_length _ _) hag patval rhs_plainP rhs_sortP).2 m)
      (fun t h => by rw [clY_ens] at h; cases h)
  have hmem : clY ∈ fF.clauses := by rw [clauses_eq]; exact List.mem_singleton_self _
  have hws : cP.sortsOf [] = some fF.args := by rw [shape.2.2.1]; rfl
  have hpl : plainPats cP clY.pats = true := by rw [clY_pats]; rfl
  have h := clause_eq_open hΓ hnn htr lookupF hmem lowY clY_pre shape.2.2.2.2.2.2.1 hws ws_e
    (by rw [clY_pats]; exact .nil) hpl pats_sortsP occ (fun t h => by rw [clY_req] at h; cases h) rhsv
    (fun t h => by rw [clY_ens] at h; cases h) (r := some ge) (fun v hv => by cases hv; exact ge_sort)
    (fun _ _ _ t h => by rw [clY_req] at h; cases h) ihrhs e0 m
  unfold TiePair.app
  rw [← symApp_plus (E := 33), ← koreList_plus_fun (E := 33), ← den_plus (E := 33)]
  exact h

/-! ## The expectation (C7 form (c)) -/

/-- **The text determines no value of `f()`**: over all H, the reading's theory with the step's
closure entails neither that `f()` has no element nor that it is any value of its sort. At
`HookParams.none`, the model in which Empty holds `e` makes `f()` the element of `g(e)`, which is
no value of c. -/
theorem f_undetermined :
    ¬ (∀ H : HookParams, (Γc (cH H) ∪ Γstep (cH H)) ⊧ (TiePair.app (cH H) fS [] ≡ ⊥)) ∧
    ∀ v, c.sortOf v = some fF.result →
      ¬ (∀ H : HookParams, (Γc (cH H) ∪ Γstep (cH H)) ⊧ (TiePair.app (cH H) fS [] ≡ den (cH H) v)) := by
  obtain ⟨M, hM, I, hP, hc⟩ := model
  have hΓP : I ⊧ᴵP Γ cP := fun φ hφ => hP φ (Or.inl (Or.inl hφ))
  have hD := defOK hΓP
  have hspec := elemOf_spec hΓP ge_sort KoreAML.val0
  have hfe : ∀ m, (TiePair.app c fS []).interpret I KoreAML.val0 m ↔ m = elemOf cP I ge := fun m =>
    (f_is_ge hΓP _ m).trans (by rw [← den_plus (E := 33)]; exact hspec.1 m)
  refine ⟨fun h => ?_, fun v hv h => ?_⟩
  · have h1 := h HookParams.none hc KoreAML.val0 (elemOf cP I ge)
    rw [cH_none, KoreAML.interp_equal hD] at h1
    have := ((h1 (elemOf cP I ge)).mp ((hfe _).mpr rfl))
    simp at this
  · have h1 := h HookParams.none hc KoreAML.val0 (elemOf cP I ge)
    rw [cH_none, KoreAML.interp_equal hD] at h1
    have hvP : cP.sortOf v = some fF.result := sortOf_plus hv
    have hspecv := elemOf_spec hΓP hvP KoreAML.val0
    have hm := (h1 (elemOf cP I ge)).mp ((hfe _).mpr rfl)
    rw [← den_plus (E := 33)] at hm
    have heq : elemOf cP I ge = elemOf cP I v := (hspecv.1 _).mp hm
    obtain ⟨-, -, -, hg, -, -, -, -, hno⟩ := hypSound_of_core coreP
    haveI : OvlOK cP := hno
    have htr := (sortCtx_of_all (hypSound_of_core coreP).1 (hypSound_of_core coreP).2.1 (OvlOK.ovlCase hno)).trans
    have := values_apart hΓP hg htr (apartSort_of_sorted hg ge_sort) ge_sort hvP heq
    rw [← this, ge_not_c] at hv
    cases hv

end KCore.TieClauseRhsEmptyC

/-- info: 'KCore.TieClauseRhsEmptyC.f_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.TieClauseRhsEmptyC.f_undetermined

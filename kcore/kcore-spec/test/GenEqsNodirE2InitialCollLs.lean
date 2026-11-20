/-
  Sentence 360 of e2-initial-coll.kompile.kore, `initLsCell() = <ls>(initLtCell())`, of the
  no-direction class of its tie (`test/TieE2InitialColl.lean`, `classes`), and sentence 163, the
  `functional` axiom of `initLsCell`, in one model of the theory, for every interpretation H of the
  parameters. Run from the package root: `lake env lean -j1 test/GenEqsNodirE2InitialCollLs.lean`.

  The text is the construct fixture e2-initial-coll, by K 7.1.337's kompile: a configuration whose
  cell `<ls>` holds the List collection of the cell `<lt>` (`multiplicity="*" type="List"
  initial=""`). Γ lacks `initLsCell`: no sentence with a direction and no equation of a function of
  Γ applies it. Γ has `initLtCell`, the initializer of the collection: a function of the semantics
  (symbol 438, total, of no argument, of the sort `LtCellList`), whose equation (sentence 361) is
  one of Γ's. The right side of sentence 360 applies the constructor `<ls>` (symbol 418, from
  `LtCellList` to `LsCell`) to `initLtCell()`, so it states the value of the symbol Γ lacks from
  Γ's symbols: in every model of Γ it denotes one element, `<ls>` of the value of `initLtCell()`.

  The model (`GenEqs.model_with_inits_step`) is a model of `Γc` with the step's closure, whose steps
  at configurations are `Step`'s, with `initLsCell` (no symbol of the semantics, so no premise of
  the theory names it) given the value `<ls>(v)`, where `v` is the value evaluation gives
  `initLtCell` at no argument (`FnHyp`'s totality, `fnHypH`). In that model `initLtCell()` denotes
  `v` (`Faithful.eval_den4_coreCl`) and `<ls>(initLtCell())` denotes `<ls>(v)`
  (`GenEqs.InitModel.ctor`), the value `initLsCell()` denotes (`GenEqs.InitModel.name`): so the
  equation holds (`GenEqs.NodEqn`, at the one, empty, list of values of its variables), and so does
  the `functional` axiom (`GenEqs.NodFun`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore ML Faithful KoreAML KCore.Parse KCore.GenEqs

namespace GenEqsNodirE2InitialCollLs

definition_of defn from "f2-examples/e2-initial-coll.kompile.kore"
user_axioms U from "f2-examples/e2-initial-coll.kompile.kore" module "C"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## `FnHyp` under every H, as the tie has it -/

def callOrder : List Nat := [435, 436, 437, 438, 441, 439, 440]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl_nil H)

/-- The clauses bind no variable by `\exists`. -/
theorem noExs : (c.fns.all fun f => f.clauses.all fun cl => cl.exs.isEmpty) = true := by decide +kernel

/-! ## The sentences -/

/-- `initLtCell()`, the right side's argument. -/
def ltApp : Kore.Pattern := .app ⟨⟨"LblinitLtCell"⟩⟩ [] []
/-- `<ls>(initLtCell())`, the right side. -/
def lsRhs : Kore.Pattern := .app ⟨⟨"Lbl'-LT-'ls'-GT-'"⟩⟩ [] [ltApp]

/-- **Sentence 360, as the account's scan reads it**: the equation of `initLsCell`, of no pattern,
with the right side `<ls>(initLtCell())`. -/
theorem eqn360 : (scanEqn (.axiom U.ax360.ax)).map (fun e => (e.fn, e.pats, e.rhs)) =
    some ("LblinitLsCell", [], lsRhs) := by decide +kernel

/-- **Sentence 163**: the `functional` axiom of `initLsCell`, at the sort `LsCell`. -/
theorem fun163 : nodFunctional? U.ax163.ax = some ("LblinitLsCell", (Kore.KSort.ctor ⟨⟨"SortLsCell"⟩⟩ [])) := by decide +kernel

theorem idx360 : U.ax360.index = 360 ∧ U.ax163.index = 163 := by decide +kernel
/-- The two are the user module's axioms of these indices. -/
theorem sel_eq : U.all.filter (fun ad => ad.index == 163 || ad.index == 360) = [U.ax163, U.ax360] := by kernel_rfl
theorem mem360 : U.ax360 ∈ U.all ∧ U.ax163 ∈ U.all :=
  ⟨(List.mem_filter.mp (sel_eq ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _))).1,
    (List.mem_filter.mp (sel_eq ▸ List.mem_cons_self ..)).1⟩

/-- **The no-direction class of the tie holds both** (`test/TieE2InitialColl.lean`, `classes`), and
each applies `initLsCell`, a symbol Γ lacks. -/
theorem absent : [U.ax163, U.ax360].all (fun ad => !(appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true := by
  decide +kernel

/-! ## The symbols -/

/-- `initLsCell` is no symbol of the registry or of the semantics, nor `inj` or `Lblite`, nor the
head of an instance-named symbol. -/
theorem ls_free : (regSymNames ++ c.symNames).contains "LblinitLsCell" = false ∧ c.instHeadFree "LblinitLsCell" = true := by
  decide +kernel

/-- `<ls>`: the constructor 418, from `LtCellList` (58) to `LsCell` (39). -/
theorem ls_ctor : lookupSig c.ctorSigs 418 = some ⟨418, [58], 39⟩ ∧ c.symName 418 = "Lbl'-LT-'ls'-GT-'" ∧
    instDecode? "Lbl'-LT-'ls'-GT-'" = none := by decide +kernel

/-- `LsCell` is the sort `SortLsCell` names. -/
theorem ls_sort : armSrt c (Kore.KSort.ctor ⟨⟨"SortLsCell"⟩⟩ []) = some 39 := by decide +kernel

/-- `initLtCell`: the function 438 of the semantics, total, of no argument, of the sort
`LtCellList` (58). -/
theorem lt_find : (c.fns.find? (·.label == 438)).map (fun f => (f.label, f.total, f.args, f.result)) =
    some (438, true, [], 58) := by decide +kernel

theorem lt_name : c.symName 438 = "LblinitLtCell" ∧ instDecode? "LblinitLtCell" = none := by decide +kernel

/-! ## The model -/

/-- The value of `initLsCell` at `v`, the value of `initLtCell`: `<ls>(v)`. -/
def G (v : GroundTerm) : String → List GroundTerm → Option GroundTerm :=
  fun n _ => if n = "LblinitLsCell" then some (.ctor 418 [v]) else none

/-- **For every H, one model of `Γc ∪ Γstep` of `c.withHooks H`, whose steps at configurations are
`Step`'s, in which sentence 360 (`initLsCell() = <ls>(initLtCell())`) holds at every list of values
of its variables' sorts, and sentence 163 (`initLsCell`'s `functional` axiom) holds**; read as the
account reads the text. -/
theorem nodir_360 (H : HookParams) :
    ∃ I : ML.Interpretation KoreAML.Sym Faithful.Model.Elem,
      (I ⊧ᴵP (Faithful.Γc (cH H) ∪ Faithful.Γstep (cH H))) ∧
      (∀ x y : Config (cH H), Step (cH H) x y ↔ ¬ (I ⊧ᴵ (den (cH H) x.val ⇒ ∼ KoreAML.sNext (den (cH H) y.val)))) ∧
      (∃ ad ∈ U.all, ad.index = 360 ∧ ∃ e, scanEqn (.axiom ad.ax) = some e ∧ NodEqn (cH H) I e) ∧
      (∃ ad ∈ U.all, ad.index = 163 ∧ ∃ L S, nodFunctional? ad.ax = some (L, S) ∧ NodFun (cH H) I L S) := by
  have h := coreOKH H
  have hf := fnHypH H
  obtain ⟨fn, hfind, hfe⟩ := Option.map_eq_some_iff.mp lt_find
  simp only [Prod.mk.injEq] at hfe
  obtain ⟨hlab, htot, hargs, hres⟩ := hfe
  have hfn : fn ∈ (cH H).fns := List.mem_of_find?_eq_some hfind
  have hlook : (cH H).lookupFn 438 = some fn := by
    rw [Semantics.lookupFn_eq]
    unfold Semantics.allFns
    rw [List.find?_append, show (cH H).fns.find? (·.label == 438) = some fn from hfind]
    rfl
  -- the value of `initLtCell` at no argument
  obtain ⟨v, hev⟩ := hf.2.1 fn hfn htot [] (by rw [hargs]; rfl)
  rw [hlab] at hev
  haveI hov : OvlOK (cH H) := ovlOK_of_core h
  obtain ⟨hok, hsr, -, -, hph, -, -, -, -⟩ := hypSound_of_core h
  have hnoEx : (cH H).FnsNoExs := Semantics.fnsNoExs_of_all noExs
  have hokCl : (cH H).sortedOKCl = true := Semantics.sortedOKCl_of_sortedOK_noExs hok hnoEx
  have hfa : (cH H).faithCoreOK = true := (Semantics.coreOK_parts h).2.1
  have hsc : SortCtx (cH H) := sortCtx_of_allCl hokCl hsr (OvlOK.ovlCase hov)
  have hvs : (cH H).sortOf v = some 58 := hres ▸ Eval.sorted hsc hev hlook (by rw [hargs]; rfl) rfl
  have hlsS : (cH H).sortOf (.ctor 418 [v]) = some 39 :=
    nod_sortOf_ctor (k := ⟨418, [58], 39⟩) ls_ctor.1 (by simp [Semantics.sortsOf, hvs])
  -- the model
  obtain ⟨I, hM, hstep⟩ := model_with_inits_step (cH H) h hf (· = "LblinitLsCell") (fun _ => 0) (G v)
    (fun n hn => by subst hn; exact ⟨ls_free.1, by decide, by decide, by decide, ls_free.2⟩)
  have hIc : I ⊧ᴵP Γc (cH H) := fun φ hφ => hM.sat φ (Or.inl hφ)
  -- `initLtCell()` denotes `v`
  have hLt : DenV (cH H) I (KoreAML.den ltApp) v := by
    refine ⟨⟨58, hvs⟩, fun ρ m => ?_⟩
    have hden := eval_den4_coreCl hIc hokCl hsr hfa hph hf.2.2.2.2.1.2
      (HoldsShape.preReadAll_of_core h hIc) hev hlook (by rw [hargs]; rfl) ρ m
    have hnm : (cH H).symName 438 = "LblinitLtCell" := lt_name.1
    have hinst : instDecode? ((cH H).symName 438) = none := by rw [hnm]; exact lt_name.2
    rw [symApp_noInst (c := cH H) (f := 438) hinst, hnm] at hden
    exact hden.trans (hM.vals v 58 hvs ρ m)
  -- `<ls>(initLtCell())` and `initLsCell()` denote `<ls>(v)`
  have hR : DenV (cH H) I (KoreAML.den lsRhs) (.ctor 418 [v]) := by
    have := hM.ctor (.cons hLt .nil) hlsS
    rw [show (cH H).symName 418 = "Lbl'-LT-'ls'-GT-'" from ls_ctor.2.1] at this
    unfold lsRhs; rw [armDen_app0]; exact this
  have hL : DenV (cH H) I (KoreAML.appList (symP "LblinitLsCell") []) (.ctor 418 [v]) :=
    hM.name rfl .nil rfl (by simp [G]) hlsS
  refine ⟨I, hM.sat, hstep, ⟨U.ax360, mem360.1, idx360.1, ?_⟩, ⟨U.ax163, mem360.2, idx360.2, ?_⟩⟩
  · obtain ⟨e, he, hfe⟩ := Option.map_eq_some_iff.mp eqn360
    refine ⟨e, he, ?_⟩
    cases e
    simp only [Prod.mk.injEq] at hfe
    obtain ⟨rfl, rfl, rfl⟩ := hfe
    intro ws hws
    have hws' : NodVals (cH H) [] ws := hws
    cases hws'
    show I ⊧ᴵ (KoreAML.den (.app ⟨⟨"LblinitLsCell"⟩⟩ [] []) ≡ KoreAML.den lsRhs)
    rw [armDen_app0]
    exact hM.eqn hL hR
  · refine ⟨"LblinitLsCell", (Kore.KSort.ctor ⟨⟨"SortLsCell"⟩⟩ []), fun163, fun s hs y => ?_⟩
    rw [show armSrt (cH H) (Kore.KSort.ctor ⟨⟨"SortLsCell"⟩⟩ []) = some 39 from ls_sort] at hs
    cases hs
    exact hM.functional hL hlsS y

/-- info: 'GenEqsNodirE2InitialCollLs.nodir_360' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodir_360

end GenEqsNodirE2InitialCollLs

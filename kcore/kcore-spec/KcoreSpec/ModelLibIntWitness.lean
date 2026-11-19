/-
  KCore. A semantics that meets every condition of `coreOK` but `genWf`, and `FnHyp`, whose `Γ` has
  no model because a sort of domain values is a constructor sort: so `SoundC` fails of it
  (`not_sound`), and `genWf` cannot be left out of `coreOK`.

  The library's sorts below KItem are Int, with the library constructor `#KConfigValue : → Int`.
  A library sort with a generator is a constructor sort (`consSorts`, through `libCtorSorts`), so
  `Γ` states Int's no-junk axiom (`ΓCons`): every element of Int is `#KConfigValue()`'s, one element
  (it is a value, `den_single`). But the literals 0 and 1 are values of Int, each an element of Int
  (`elemOf_spec`), and distinct values of Int share no element (`dom_apart`, Int being in
  `distinctSorts`). genWf's third part (a constructor sort is not Int) refuses exactly this; nothing
  else of `coreOK` reads it. The decidable facts are kernel decisions.
-/
import KcoreSpec.Sound
import KcoreSpec.ModelUndefRhsWitness

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace LibIntWitness

open ML Faithful
open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

def c : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int], ctors := [⟨kconfigValue, [], Srt.int⟩] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem sortedOK : c.sortedOK = true := by decide +kernel

/-- `c` has no function: `FnHyp` holds. -/
theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

set_option maxHeartbeats 1000000 in
/-- Every condition of `coreOK` but `genWf` holds, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧ namesNumbered c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧
    patHeadsOK c = true ∧ Model.namesApartK c = true ∧ Model.LitsApart c = true ∧
    Model.sortsNumbered c = true ∧ Model.itesApart c = true ∧ Model.kindsApart c = true ∧
    Model.ctorsOnce c = true ∧ Model.fnsApart c = true ∧ FnHyp c :=
  ⟨sortedOK, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, fnHyp⟩

theorem not_genWf : genWf c = false := by decide +kernel

/-- Int is a constructor sort of `c`. -/
theorem int_cons : (consSorts c).contains Srt.int = true := by decide +kernel

/-- Two values of Int, and the constructor's. -/
def v0 : GroundTerm := .dv Srt.int (.int 0)
def v1 : GroundTerm := .dv Srt.int (.int 1)
def vx : GroundTerm := .ctor kconfigValue []

theorem v0_sort : c.sortOf v0 = some Srt.int := by decide +kernel
theorem v1_sort : c.sortOf v1 = some Srt.int := by decide +kernel
theorem vx_sort : c.sortOf vx = some Srt.int := by decide +kernel
theorem den_x : den c vx = KoreAML.sym (.symbol (c.symName kconfigValue)) := by decide +kernel

/-- Int's no-junk axiom. -/
def noJunkAx : KoreAML.P := (KoreAML.Cons.noJunkItem (c.sortName Srt.int) ((c.gens Srt.int).map (Gen.toK c))).pat

/-- With no free variable it has no guard: `⊤ → (#KConfigValue ∨ ⊥ = ⟦Int⟧)`. -/
theorem noJunkAx_eq :
    noJunkAx = (⊤ ⇒ (KoreAML.sOr (KoreAML.Cons.sortP (c.sortName Srt.int)) (KoreAML.sym (.symbol (c.symName kconfigValue)))
      (KoreAML.sBot (KoreAML.Cons.sortP (c.sortName Srt.int))) ≡ KoreAML.inhOf (KoreAML.Cons.sortP (c.sortName Srt.int)))) := by
  decide +kernel

theorem noJunkAx_mem_any : (consItemsK c).any (fun it => decide (it.pat = noJunkAx)) = true := by decide +kernel

theorem noJunkAx_mem : noJunkAx ∈ ΓCons c := by
  obtain ⟨it, hit, h⟩ := List.any_eq_true.mp noJunkAx_mem_any
  exact Or.inl ⟨it, hit, of_decide_eq_true h⟩

/-- **`Γ c` has no model.** -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have hD := defOK hI
  have hnj := hI noJunkAx (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr noJunkAx_mem))))))
  rw [noJunkAx_eq] at hnj
  have hgr := (KoreAML.interp_equal hD).mp (interpret_impl.mp (hnj KoreAML.val0 default) (by simp [Pattern.top]))
  have hx := (elemOf_spec hI vx_sort KoreAML.val0).1
  -- every value of Int is the constructor's element
  have hin : ∀ v, c.sortOf v = some Srt.int → elemOf c I v = elemOf c I vx := fun v hv => by
    have h1 := (elemOf_spec hI hv KoreAML.val0).2
    have h2 := (hgr (elemOf c I v)).mpr h1
    rw [KoreAML.interp_sOr] at h2
    have h3 : I.evalSymb (.symbol (c.symName kconfigValue)) (elemOf c I v) := by
      rcases h2.2 with h3 | h3
      · exact h3
      · unfold KoreAML.sBot at h3
        rw [KoreAML.interp_sNot, KoreAML.interp_sTop hD (by rfl)] at h3
        exact absurd h3.2 h3.1
    exact (hx _).mp (by rw [den_x]; exact h3)
  have he : elemOf c I v0 = elemOf c I v1 := (hin v0 v0_sort).trans (hin v1 v1_sort).symm
  have h0 := ((elemOf_spec hI v0_sort KoreAML.val0).1 (elemOf c I v0)).mpr rfl
  have h1 := ((elemOf_spec hI v1_sort KoreAML.val0).1 (elemOf c I v0)).mpr he
  exact dom_apart hI (by decide +kernel) v0_sort v1_sort (by decide) KoreAML.val0 (elemOf c I v0) ⟨h0, h1⟩

/-- **Soundness fails** of `c`, which meets every condition of `coreOK` but `genWf`, and `FnHyp`. -/
theorem not_sound : ¬ SoundC c := fun h => by
  obtain ⟨⟨M, hM, I, hI⟩, -⟩ := h
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl (Or.inl hφ)))

end LibIntWitness

end KCore

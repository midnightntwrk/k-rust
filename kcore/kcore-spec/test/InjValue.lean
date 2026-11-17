/-
  `inj_value`, `inj_no_element` and `inj_value_unique` (KcoreSpec/InjValue.lean) at a definition
  with a model. Run from the package root: `lake env lean -j1 test/InjValue.lean`. Kernel-checked
  (`decide +kernel`).

  `InjValueFx.base2` has Int and Bool below KItem, the cells of a `<k>` configuration, no function
  and no rule. `coreOK` holds and `FnHyp` is proved (there is no function and no open generator),
  so `Γ base2` has a model (`has_model_choice`).

  - `inj_value_instance`: `Γ base2` has a model, and in every model an element of Int whose
    injection into KItem is the element of `inj{Int,KItem}(3)` is the element of 3, and no element
    of Int has the element of `inj{Bool,KItem}(true)` as its injection.
  - `int_not_kT`: no value of Int injects to `inj{Bool,KItem}(true)` where Bool is not below Int.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.CE.InjValueFx

open ML Faithful GroundTerm
open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

def base2 : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

abbrev v3 : GroundTerm := .dv Srt.int (.int 3)
abbrev vT : GroundTerm := .dv Srt.bool (.bool true)
abbrev k3 : GroundTerm := .inj Srt.int Srt.kitem v3
abbrev kT : GroundTerm := .inj Srt.bool Srt.kitem vT

/-- No value of Int injects to `inj{Bool,KItem}(true)`, where Bool is not below Int. -/
theorem int_not_kT {c : Semantics} (hns : (Srt.bool, Srt.int) ∉ c.subsorts) {z : GroundTerm}
    (hz : c.sortOf z = some Srt.int) : injNormal Srt.int Srt.kitem z ≠ kT := by
  intro he
  cases z with
  | inj a' b' w =>
    obtain ⟨hsub, -, -, hb⟩ := sortOf_inj.mp hz
    simp only [injNormal] at he
    injection he with ha _ _
    subst ha; subst hb
    exact hns hsub
  | ctor f ts => simp [injNormal] at he
  | dv s l => simp [injNormal] at he
  | map s es => simp [injNormal] at he
  | set s es => simp [injNormal] at he
  | list s es => simp [injNormal] at he

theorem base2_core : base2.coreOK = true := by decide_cheap

theorem base2_fnHyp : FnHyp base2 :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (fun _ h => absurd h List.not_mem_nil)⟩

theorem k3_sorted : base2.sortOf k3 = some Srt.kitem := by decide +kernel
theorem kT_sorted : base2.sortOf kT = some Srt.kitem := by decide +kernel
theorem base2_sub : base2.subsorts.contains (Srt.int, Srt.kitem) = true := by decide +kernel
theorem base2_nsub : (Srt.bool, Srt.int) ∉ base2.subsorts := by decide +kernel

/-- `Γ base2` has a model, and in every model: an element of Int whose injection into KItem is the
element of `inj{Int,KItem}(3)` is the element of 3, and no element of Int has the element of
`inj{Bool,KItem}(true)` as its injection. -/
theorem inj_value_instance :
    (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ base2) ∧
    ∀ (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M), (I ⊧ᴵP Γ base2) →
      ∀ e : M, InS I (base2.sortName Srt.int) e →
        (GS I (base2.sortName Srt.kitem) (.inj (base2.sortName Srt.int)) [e] (elemOf base2 I k3) →
          e = elemOf base2 I v3) ∧
        ¬ GS I (base2.sortName Srt.kitem) (.inj (base2.sortName Srt.int)) [e] (elemOf base2 I kT) := by
  constructor
  · obtain ⟨M, i, I, hI, -⟩ := has_model_choice base2 base2_core base2_fnHyp (Step base2)
      (fun _ _ h => h) (fun _ _ _ _ h _ => absurd h.mem List.not_mem_nil) (fun _ _ _ _ h => absurd h.mem List.not_mem_nil)
    exact ⟨M, i, I, fun φ hφ => hI φ (Or.inl (Or.inl hφ))⟩
  · intro M _ I hI e he
    refine ⟨fun hm => ?_, inj_no_element base2_core hI base2_sub kT_sorted (fun w hw => int_not_kT base2_nsub hw) he⟩
    obtain ⟨w, hw, hvw, rfl⟩ := inj_value base2_core hI base2_sub k3_sorted he hm
    have : w = v3 := inj_value_unique base2_core hw (sortOf_int 3) (by rw [← hvw]; rfl)
    rw [this]

end KCore.CE.InjValueFx

#print axioms KCore.CE.inj_defined
#print axioms KCore.CE.inj_value
#print axioms KCore.CE.inj_value_unique
#print axioms KCore.CE.inj_value_at
#print axioms KCore.CE.inj_value_pat
#print axioms KCore.CE.inj_no_element
#print axioms KCore.CE.condOK_inj_equals
#print axioms KCore.CE.InjValueFx.inj_value_instance

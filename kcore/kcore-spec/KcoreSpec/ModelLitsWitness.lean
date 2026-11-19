/-
  KCore. A semantics that meets every condition of `coreOK` but `LitsApart`, and `FnHyp`, whose `Γ`
  has no model because a token sort of the library is Int: so `SoundC` fails of it (`not_sound`),
  and `LitsApart` cannot be left out of `coreOK`.

  The library's token sorts are Int. A token is then a literal of Int (`dvOK`) besides the
  integers, so the token `1` and the integer `1` are two values of Int (`v1`, `t1`). The KORE
  writes a literal by its sort and its text only (`Lit.text`), and both texts are `1`: the two
  values denote one pattern (`den_eq`), hence one element (`elemOf_spec`). But distinct values of
  Int share no element (`dom_apart`, Int being in `distinctSorts`). `LitsApart` refuses exactly
  this; nothing else of `coreOK` reads it (`meets_others`). The decidable facts are kernel decisions.
-/
import KcoreSpec.Sound
import KcoreSpec.ModelUndefRhsWitness

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace LitsWitness

open ML Faithful
open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

def c : Semantics :=
  { lib := { tokenSorts := [Srt.int] }
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
/-- Every condition of `coreOK` but `LitsApart` holds, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧ namesNumbered c = true ∧ genWf c = true ∧ collSortsOK c = true ∧
    collsOK c = true ∧ patHeadsOK c = true ∧ Model.namesApartK c = true ∧
    Model.sortsNumbered c = true ∧ Model.itesApart c = true ∧ Model.kindsApart c = true ∧
    Model.ctorsOnce c = true ∧ Model.fnsApart c = true ∧ FnHyp c :=
  ⟨sortedOK, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, fnHyp⟩

theorem not_litsApart : Model.LitsApart c = false := by decide +kernel

/-- The integer `1` and the token `1`, both values of Int. -/
def v1 : GroundTerm := .dv Srt.int (.int 1)
def t1 : GroundTerm := .dv Srt.int (.tok "1")

theorem v1_sort : c.sortOf v1 = some Srt.int := by decide +kernel
theorem t1_sort : c.sortOf t1 = some Srt.int := by decide +kernel

/-- Both are written `\dv{SortInt}("1")`. -/
theorem den_eq : den c t1 = den c v1 := by decide +kernel

/-- **`Γ c` has no model.** -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have h1 := ((elemOf_spec hI v1_sort KoreAML.val0).1 (elemOf c I v1)).mpr rfl
  have h2 : (den c t1).interpret I KoreAML.val0 (elemOf c I v1) := by rw [den_eq]; exact h1
  exact dom_apart hI (by decide +kernel) v1_sort t1_sort (by decide) KoreAML.val0 (elemOf c I v1) ⟨h1, h2⟩

/-- **Soundness fails** of `c`, which meets every condition of `coreOK` but `LitsApart`, and `FnHyp`. -/
theorem not_sound : ¬ SoundC c := fun h => by
  obtain ⟨⟨M, hM, I, hI⟩, -⟩ := h
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl (Or.inl hφ)))

end LitsWitness

end KCore

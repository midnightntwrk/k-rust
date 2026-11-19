/-
  KCore. A semantics that meets every condition of `coreOK` but `collsOK`, and `FnHyp`, whose `Γ`
  has no model because a collection's unit is not implemented by the library's unit: so `SoundC`
  fails of it (`not_sound`), and `collsOK` cannot be left out of `coreOK`.

  The cells and one list collection `S` of the definition's own, of KItem, whose element and
  concatenation parameters are implemented by the library list's, and whose unit parameter `uS`
  is implemented by the library list's element symbol (`collSymsOK` asks for its unit). The
  element symbol takes one argument, so at no arguments it has no value, and the parameter's
  graph in `ΓDomains` says that `uS()` denotes nothing (`paramVal_unit`). But the empty list of `S`
  is a value of `S` (`v_sort`), written `uS()` (`kore_v`), and every value denotes one element
  (`elemOf_spec`). With the unit implemented by the library's unit, `coreOK` holds (`c0_coreOK`).
  The decidable facts are kernel decisions.
-/
import KcoreSpec.CoreDecide
import KcoreSpec.Sound
import KcoreSpec.ModelUndefRhsWitness

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace CollUnitWitness

open ML Faithful

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]
def ownCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 3, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 4, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def S : Srt := nRegSorts + 2
def uS : Sym := nRegSyms + 5
def eS : Sym := nRegSyms + 6
def cS : Sym := nRegSyms + 7

/-- The cells and the list collection `S` of KItem, its unit parameter implemented by `unit`. -/
def withUnit (unit : Sym) : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
    sortNames := ["KCell", "KCellOpt", "S"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisS", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lbl'Stop'S", "LblSItem",
      "Lbl'Unds'S'Unds'"]
    userSorts := cellSorts ++ [S]
    ctors := ownCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := []
    params := [{ sig := ⟨uS, [], S⟩, impl := some unit },
      { sig := ⟨eS, [Srt.kitem], S⟩, impl := some (builtinColl .list).elem },
      { sig := ⟨cS, [S, S], S⟩, impl := some (builtinColl .list).concat }]
    colls := [⟨S, .list, Srt.kitem, none, uS, eS, cS⟩] }

/-- The unit parameter implemented by the library list's element symbol. -/
def c : Semantics := withUnit (builtinColl .list).elem

/-- The unit parameter implemented by the library list's unit. -/
def c0 : Semantics := withUnit (builtinColl .list).unit

set_option maxHeartbeats 4000000 in
theorem c0_coreOK : c0.coreOK = true := by decide_coreOK

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem sortedOK : c.sortedOK = true := by decide +kernel

/-- `c` has no function: `FnHyp` holds. -/
theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

set_option maxHeartbeats 1000000 in
/-- Every condition of `coreOK` but `collsOK` holds, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧ namesNumbered c = true ∧ genWf c = true ∧ collSortsOK c = true ∧
    patHeadsOK c = true ∧ Model.namesApartK c = true ∧ Model.LitsApart c = true ∧
    Model.sortsNumbered c = true ∧ Model.itesApart c = true ∧ Model.kindsApart c = true ∧
    Model.ctorsOnce c = true ∧ Model.fnsApart c = true ∧ FnHyp c :=
  ⟨sortedOK, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, fnHyp⟩

theorem not_collsOK : collsOK c = false := by decide +kernel

/-- The empty list of `S`. -/
def v : GroundTerm := .list S []

theorem v_sort : c.sortOf v = some S := by decide +kernel

/-- It is written `uS()`. -/
theorem kore_v : v.kore c = symApp c uS (GroundTerm.koreList c []) := by decide +kernel

/-- The unit parameter has no value at no arguments. -/
theorem paramVal_unit : c.paramVal uS [] = none := by decide +kernel

def kU : ParamSig := { sig := ⟨uS, [], S⟩, impl := some (builtinColl .list).elem }

theorem kU_mem : kU ∈ c.params := List.mem_cons_self

/-- **`Γ c` has no model.** -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have hax := sat_dom hI (Or.inr (Or.inl ⟨kU, [], kU_mem, by decide +kernel, rfl⟩))
  have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax KoreAML.val0 default) (elemOf c I v)
  have h1 := ((elemOf_spec hI v_sort KoreAML.val0).1 (elemOf c I v)).mpr rfl
  have h2 : (KoreAML.den (symApp c uS (GroundTerm.koreList c []))).interpret I KoreAML.val0 (elemOf c I v) := by
    rw [← kore_v]; exact h1
  have h3 := hgr.mp h2
  simp only [kU, paramVal_unit] at h3
  exact interpret_bottom.mp h3

/-- **Soundness fails** of `c`, which meets every condition of `coreOK` but `collsOK`, and `FnHyp`. -/
theorem not_sound : ¬ SoundC c := fun h => by
  obtain ⟨⟨M, hM, I, hI⟩, -⟩ := h
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl (Or.inl hφ)))

end CollUnitWitness

end KCore

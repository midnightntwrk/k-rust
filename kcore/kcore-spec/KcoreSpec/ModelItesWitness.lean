/-
  KCore. A semantics that meets every condition of `coreOK` but `itesApart`, and `FnHyp`, whose `Γ`
  has no model because two parameter symbols are named like `ite` at one sort: so `SoundC` fails of
  it (`not_sound`), and `itesApart` cannot be left out of `coreOK`.

  The two parameters `Lblite{Int}` and `Lblite{Int]` take two Ints to an Int; the first is
  implemented by `_+Int_`, the second has no implementation, so it is undefined everywhere
  (`HookParams.none`). Their names differ, so `NamesApartK` holds, but `iteSort?` reads both as `ite`
  at `Int`, and `Γ` writes the application of either as `Lblite{SortInt}(…)` (`symApp`). Its graphs
  then say of `Lblite{SortInt}(1, 2)` both that it is `3` and that it is nothing (`ΓDomains`), while
  `3` denotes an element. The decidable facts are kernel decisions.
-/
import KcoreSpec.Sound

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace ItesWitness

open ML

def kIds : CellIds := { sort := nRegSorts, opt := some (nRegSorts + 1), label := nRegSyms + 2, no := some (nRegSyms + 3) }

/-- The configuration `<k> K </k>` with the generated counter, as ordinary sorts, constructors
and subsorts: the top cell's, its fragment's, the `k` cell's and the counter's. -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- `Lblite{Int}`, implemented by `_+Int_`. -/
def p1 : ParamSig := { sig := ⟨nRegSyms + 4, [Srt.int, Srt.int], Srt.int⟩, impl := some intAdd }
/-- `Lblite{Int]`, with no implementation. -/
def p2 : ParamSig := { sig := ⟨nRegSyms + 5, [Srt.int, Srt.int], Srt.int⟩ }

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblite{Int}", "Lblite{Int]"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := []
    params := [p1, p2] }

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem sortedOK : c.sortedOK = true := by decide +kernel

/-- `c` has no function: `FnHyp` holds. -/
theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_sortedOK sortedOK⟩

/-- Every condition of `coreOK` but `itesApart` holds, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.hooksApart = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    namesNumbered c = true ∧ genWf c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧
    patHeadsOK c = true ∧ Model.namesApartK c = true ∧ Model.LitsApart c = true ∧
    Model.sortsNumbered c = true ∧ Model.kindsApart c = true ∧ Model.ctorsOnce c = true ∧
    Model.fnsApart c = true ∧ FnHyp c :=
  ⟨sortedOK, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, fnHyp⟩

theorem not_itesApart : Model.itesApart c = false := by decide +kernel

def v1 : GroundTerm := .dv Srt.int (.int 1)
def v2 : GroundTerm := .dv Srt.int (.int 2)
def v3 : GroundTerm := .dv Srt.int (.int 3)

theorem v3_sort : c.sortOf v3 = some Srt.int := by decide +kernel
theorem p1_mem : p1 ∈ c.params := List.mem_cons_self ..
theorem p2_mem : p2 ∈ c.params := List.mem_cons_of_mem _ (List.mem_cons_self ..)
theorem args1 : c.sortsOf [v1, v2] = some p1.sig.args := by decide +kernel
theorem args2 : c.sortsOf [v1, v2] = some p2.sig.args := by decide +kernel
theorem val1 : c.paramVal p1.sig.name [v1, v2] = some v3 := by decide +kernel
theorem val2 : c.paramVal p2.sig.name [v1, v2] = none := by decide +kernel
theorem ite1 : iteSort? (c.symName p1.sig.name) = some "Int" := by decide +kernel
theorem ite2 : iteSort? (c.symName p2.sig.name) = some "Int" := by decide +kernel

/-- Both parameters' applications are written `Lblite{SortInt}(…)`. -/
theorem symApp_same : symApp c p1.sig.name (GroundTerm.koreList c [v1, v2]) =
    symApp c p2.sig.name (GroundTerm.koreList c [v1, v2]) := by
  unfold symApp; rw [ite1, ite2]

/-- **`Γ c` has no model.** -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have hD := defOK hI
  have ax1 := sat_dom hI (Or.inr (Or.inl ⟨p1, [v1, v2], p1_mem, args1, rfl⟩))
  have ax2 := sat_dom hI (Or.inr (Or.inl ⟨p2, [v1, v2], p2_mem, args2, rfl⟩))
  have g1 := (KoreAML.interp_equal hD).mp (ax1 KoreAML.val0 default) (elemOf c I v3)
  have g2 := (KoreAML.interp_equal hD).mp (ax2 KoreAML.val0 default) (elemOf c I v3)
  rw [val1] at g1
  rw [val2, ← symApp_same] at g2
  have h3 := ((elemOf_spec hI v3_sort KoreAML.val0).1 (elemOf c I v3)).mpr rfl
  exact g2.mp (g1.mpr h3)

/-- **Soundness fails** of `c`, which meets every condition of `coreOK` but `itesApart`, and
`FnHyp`. -/
theorem not_sound : ¬ SoundC c := fun h => by
  obtain ⟨⟨M, hM, I, hI⟩, -⟩ := h
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl (Or.inl hφ)))

end ItesWitness

end Faithful

end KCore

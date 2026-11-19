/-
  KCore. A semantics that meets every condition of `coreOK` but `sortsNumbered`, and `FnHyp`, whose
  `Γ` has no model because a sort of its values is not a numbered sort: so `SoundC` fails of it
  (`not_sound`), and `sortsNumbered` cannot be left out of `coreOK`.

  `Γ` writes a sort under its name (`Semantics.sortName`), and a sort outside the numbered ones
  (`kernelSorts`) has the empty name, which a numbered sort may also have. Here the user sort `U`,
  with the one constructor `u`, is named so, and the library's token sort `t` is the first sort
  after the numbered ones. Both are then the sort `Sort` of `Γ`: each value of `t` is an element of
  it (`ΓDomains`), so by `U`'s no-junk axiom (`ΓCons`) it is `u`'s element; but `t`'s distinct
  values `"a"` and `"b"` are distinct elements (`values_apart`). Nothing else of `coreOK` reads the
  number of a token sort. The decidable facts are kernel decisions.
-/
import KcoreSpec.Sound

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace SortsWitness

open ML

def kIds : CellIds := { sort := nRegSorts, opt := some (nRegSorts + 1), label := nRegSyms + 3, no := some (nRegSyms + 4) }

/-- The configuration `<k> K </k>` with the generated counter, as ordinary sorts, constructors
and subsorts: the top cell's, its fragment's, the `k` cell's and the counter's. -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 3, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 4, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- The user sort `U`, named with the empty name. -/
def U : Srt := nRegSorts + 2
/-- The library's token sort `t`, the first sort after the numbered ones. -/
def t : Srt := nRegSorts + 3
/-- `U`'s constructor `u`. -/
def uL : Sym := nRegSyms + 5

def c : Semantics :=
  { lib := { tokenSorts := [t] }
    sortNames := ["KCell", "KCellOpt", ""]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisU", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblu"]
    userSorts := cellSorts ++ [U]
    ctors := cellCtors ++ [⟨uL, [], U⟩]
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem sortedOK : c.sortedOK = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel

/-- `c` has no function: `FnHyp` holds. -/
theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

set_option maxHeartbeats 1000000 in
/-- Every condition of `coreOK` but `sortsNumbered` holds, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    namesNumbered c = true ∧ genWf c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧
    patHeadsOK c = true ∧ Model.namesApartK c = true ∧ Model.LitsApart c = true ∧
    Model.itesApart c = true ∧ Model.kindsApart c = true ∧ Model.ctorsOnce c = true ∧
    Model.fnsApart c = true ∧ FnHyp c :=
  ⟨sortedOK, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, fnHyp⟩

theorem not_sortsNumbered : Model.sortsNumbered c = false := by decide +kernel

/-- Two values of `t`. -/
def va : GroundTerm := .dv t (.tok "a")
def vb : GroundTerm := .dv t (.tok "b")
/-- `u`'s value. -/
def vu : GroundTerm := .ctor uL []

theorem va_sort : c.sortOf va = some t := by decide +kernel
theorem vb_sort : c.sortOf vb = some t := by decide +kernel
theorem vu_sort : c.sortOf vu = some U := by decide +kernel
theorem t_name : c.sortName t = "" := by decide +kernel
theorem den_u : den c vu = KoreAML.sym (.symbol "Lblu") := by decide +kernel
theorem genWf_ok : genWf c = true := by decide +kernel
theorem t_apart : apartSort c t = true := by decide +kernel

/-- `U`'s no-junk axiom, the translation of the text's `\or{Sort}(Lblu{}(), \bottom{Sort}())`. -/
def noJunkAx : KoreAML.P := (KoreAML.Cons.noJunkItem (c.sortName U) ((c.gens U).map (Gen.toK c))).pat

/-- With no free variable it has no guard: `⊤ → (u ∨ ⊥ = ⟦Sort⟧)`. -/
theorem noJunkAx_eq :
    noJunkAx = (⊤ ⇒ (KoreAML.sOr (KoreAML.Cons.sortP "") (KoreAML.sym (.symbol "Lblu"))
      (KoreAML.sBot (KoreAML.Cons.sortP "")) ≡ KoreAML.inhOf (KoreAML.Cons.sortP ""))) := by
  decide +kernel

theorem noJunkAx_mem_any : (consItemsK c).any (fun it => decide (it.pat = noJunkAx)) = true := by decide +kernel

theorem noJunkAx_mem : noJunkAx ∈ ΓCons c := by
  obtain ⟨it, hit, h⟩ := List.any_eq_true.mp noJunkAx_mem_any
  exact Or.inl ⟨it, hit, of_decide_eq_true h⟩

/-- **`Γ c` has no model.** -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have hD := defOK hI
  have htr := (sortCtx_of_all sortedOK srReady (OvlOK.ovlCase inferInstance)).trans
  have hnj := hI noJunkAx (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr noJunkAx_mem))))))
  rw [noJunkAx_eq] at hnj
  have hgr := (KoreAML.interp_equal hD).mp (interpret_impl.mp (hnj KoreAML.val0 default) (by simp [Pattern.top]))
  have hu := (elemOf_spec hI vu_sort KoreAML.val0).1
  -- every value of `t` is `u`'s element
  have hin : ∀ v, c.sortOf v = some t → elemOf c I v = elemOf c I vu := fun v hv => by
    have h1 := (elemOf_spec hI hv KoreAML.val0).2
    rw [t_name] at h1
    have h2 := (hgr (elemOf c I v)).mpr h1
    rw [KoreAML.interp_sOr] at h2
    have h3 : I.evalSymb (.symbol "Lblu") (elemOf c I v) := by
      rcases h2.2 with h3 | h3
      · exact h3
      · unfold KoreAML.sBot at h3
        rw [KoreAML.interp_sNot, KoreAML.interp_sTop hD (by rfl)] at h3
        exact absurd h3.2 h3.1
    exact (hu _).mp (by rw [den_u]; exact h3)
  have := values_apart hI genWf_ok htr t_apart va_sort vb_sort ((hin va va_sort).trans (hin vb vb_sort).symm)
  exact absurd this (by decide +kernel)

/-- **Soundness fails** of `c`, which meets every condition of `coreOK` but `sortsNumbered`, and
`FnHyp`. -/
theorem not_sound : ¬ SoundC c := fun h => by
  obtain ⟨⟨M, hM, I, hI⟩, -⟩ := h
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl (Or.inl hφ)))

end SortsWitness

end Faithful

end KCore

/-
  KCore. A semantics that meets every condition of `coreOK` but `kindsApart`, and `FnHyp`, whose
  `Γ` has no model because an interpreted hook is also a constructor: so `SoundC` fails of it
  (`not_sound`), and `kindsApart` cannot be left out of `coreOK`.

  The library lists the interpreted hook `ite` (`kIte`, `Lblite : Bool KItem KItem → KItem`) among
  its constructors, with the hook's own signature, so `NamesApartK` holds (one name, one
  signature); `hooksApart` reads the user's constructors only. `Γ` says of `Lblite(true, v, v)`,
  by the hook's graph (`ΓDomains`), that it is `v`; read as a constructor's application, it is the
  constructor value `Lblite(true, v, v)`. These are two distinct values of KItem, and `Γ` makes
  distinct values of KItem distinct elements (`values_apart`). The decidable facts are kernel
  decisions.
-/
import KcoreSpec.Sound

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace KindsWitness

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

/-- The interpreted hook `ite`, with its signature. -/
def iteSig : CtorSig := ⟨kIte, [Srt.bool, Srt.kitem, Srt.kitem], Srt.kitem⟩

def c : Semantics :=
  { lib := { ctors := [⟨kconfigValue, [Srt.k], Srt.kitem⟩, iteSig] }
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
theorem srReady : c.srReady = true := by decide +kernel

/-- `c` has no function: `FnHyp` holds. -/
theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

set_option maxHeartbeats 1000000 in
/-- Every condition of `coreOK` but `kindsApart` holds, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    namesNumbered c = true ∧ genWf c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧
    patHeadsOK c = true ∧ Model.namesApartK c = true ∧ Model.LitsApart c = true ∧
    Model.sortsNumbered c = true ∧ Model.itesApart c = true ∧ Model.ctorsOnce c = true ∧
    Model.fnsApart c = true ∧ FnHyp c :=
  ⟨sortedOK, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, fnHyp⟩

theorem not_kindsApart : Model.kindsApart c = false := by decide +kernel

/-- `true`. -/
def vb : GroundTerm := .dv Srt.bool (.bool true)
/-- The value `#KConfigValue(.K)`. -/
def vk : GroundTerm := .ctor kconfigValue [.ctor dotk []]
/-- The constructor value `Lblite(true, #KConfigValue(.K), #KConfigValue(.K))`. -/
def vi : GroundTerm := .ctor kIte [vb, vk, vk]

theorem vk_sort : c.sortOf vk = some Srt.kitem := by decide +kernel
theorem vi_sort : c.sortOf vi = some Srt.kitem := by decide +kernel
theorem args_sort : c.sortsOf [vb, vk, vk] = some iteSig.args := by decide +kernel
theorem iteSig_hook : iteSig ∈ hookSigs := by decide +kernel
theorem hook_ite : hook iteSig.name [vb, vk, vk] = some (some vk) := by decide +kernel
theorem genWf_ok : genWf c = true := by decide +kernel
theorem kitem_apart : apartSort c Srt.kitem = true := by decide +kernel
theorem ite_plain : instDecode? (c.symName kIte) = none := by decide +kernel

/-- **`Γ c` has no model.** -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have hD := defOK hI
  have htr := (sortCtx_of_all sortedOK srReady (OvlOK.ovlCase inferInstance)).trans
  -- the hook's graph: `Lblite(true, v, v)` is `v`
  have hax := sat_dom hI (Or.inl ⟨iteSig, [vb, vk, vk], some vk, iteSig_hook, args_sort, hook_ite, (by intro h; cases h), rfl⟩)
  have hgr := (KoreAML.interp_equal hD).mp (hax KoreAML.val0 default)
  -- its left side is the constructor value
  have hfd : ∀ m, (KoreAML.den (symApp c iteSig.name (GroundTerm.koreList c [vb, vk, vk]))).interpret I
      KoreAML.val0 m ↔ (den c vi).interpret I KoreAML.val0 m := fun m => by
    show (KoreAML.den (symApp c kIte _)).interpret I _ m ↔ _
    rw [symApp_noInst ite_plain] <;> rfl
  have he : elemOf c I vi = elemOf c I vk := by
    have h1 := (elemOf_spec hI vi_sort KoreAML.val0).1
    have h2 := (elemOf_spec hI vk_sort KoreAML.val0).1
    exact (h2 _).mp ((hgr (elemOf c I vi)).mp ((hfd _).mpr ((h1 _).mpr rfl)))
  have := values_apart hI genWf_ok htr kitem_apart vi_sort vk_sort he
  simp only [vi, vk, GroundTerm.ctor.injEq] at this
  exact absurd this.1 (by decide +kernel)

/-- **Soundness fails** of `c`, which meets every condition of `coreOK` but `kindsApart`, and
`FnHyp`. -/
theorem not_sound : ¬ SoundC c := fun h => by
  obtain ⟨⟨M, hM, I, hI⟩, -⟩ := h
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl (Or.inl hφ)))

end KindsWitness

end Faithful

end KCore

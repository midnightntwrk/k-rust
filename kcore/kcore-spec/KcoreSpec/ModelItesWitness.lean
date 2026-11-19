/-
  KCore. A semantics with two parameters named `Lblite{Int}` and `Lblite{Int]`, both taking two
  Ints to an Int, the first implemented by `_+Int_`, the second without an implementation. The
  decoder of instance names (`instDecode?`) reads the first as the head `Lblite` at `Int` and the
  second, whose sort list no `}` closes, as no instance (`ite1`, `ite2`), and `Γ` writes their applications at two heads,
  `Lblite{SortInt}(…)` and `Lblite{Int]}(…)` (`symApp_apart`). The semantics meets every condition
  of `coreOK`, `itesApart` among them (`itesApart_holds`, `coreOK_holds`), and `FnHyp`, so it is
  sound (`sound`, by `sound_hyp`).

  Two symbols of `kernelSyms` that the decoder reads as one instance are one symbol (`instsApart`,
  from `namesApartK` and the decoder's exactness), so no semantics meeting `namesApartK` names two
  symbols at one head and the same sorts; `itesApart` asks no such condition. The decidable facts
  are kernel decisions.
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
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

/-- Every condition of `coreOK` but `itesApart` holds, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.hooksApart = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    namesNumbered c = true ∧ genWf c = true ∧ collSortsOK c = true ∧ collsOK c = true ∧
    patHeadsOK c = true ∧ Model.namesApartK c = true ∧ Model.LitsApart c = true ∧
    Model.sortsNumbered c = true ∧ Model.kindsApart c = true ∧ Model.ctorsOnce c = true ∧
    Model.fnsApart c = true ∧ FnHyp c :=
  ⟨sortedOK, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, fnHyp⟩

/-- `itesApart` holds: `Lblite{Int}` is the one instance name, at the numbered sort `Int`. -/
theorem itesApart_holds : Model.itesApart c = true := by decide +kernel

theorem ite1 : instDecode? (c.symName p1.sig.name) = some ("Lblite", ["Int"]) := by decide +kernel
theorem ite2 : instDecode? (c.symName p2.sig.name) = none := by decide +kernel

/-- The two parameters' applications are written at two heads. -/
theorem symApp_apart (args : List Kore.Pattern) :
    symApp c p1.sig.name args = .app ⟨⟨"Lblite"⟩⟩ [KoreAML.srt "Int"] args ∧
      symApp c p2.sig.name args = .app ⟨⟨"Lblite{Int]"⟩⟩ [] args := by
  constructor
  · exact symApp_inst ite1
  · exact symApp_noInst ite2

theorem overloadsOK_holds : c.overloadsOK = true := by decide +kernel

/-- **`c` meets `coreOK`.** -/
theorem coreOK_holds : c.coreOK = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -⟩ := meets_others
  have h9' : Model.collsNotCtors c = true := by decide +kernel
  simp only [Semantics.coreOK, Semantics.faithCoreOK, h1, h2, h3, h4, h5, h6, h7, h8, h9, h9', h10, h11,
    h12, h13, h14, h15, itesApart_holds, overloadsOK_holds, Bool.and_self]

/-- **`c` is sound.** -/
theorem sound : SoundC c := sound_hyp c coreOK_holds fnHyp

end ItesWitness

end Faithful

end KCore

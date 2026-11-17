/-
  `RangeBelow` (SubjectReduction.lean): every Range value of a semantics is a KItem. Kernel-checked
  instances of the lemmas that give it and read it, run from the package root:
  `lake env lean test/RangeBelow.lean`.
  - `cR` (the Range constructor, Int and Range below KItem, the `k` cell): `coreOK` holds, and
    `rangeBelow_of_core`, `rangeBelow_of_sound`, `rangeBelow_of_model` and `rangeBelow_of_genWf`
    each give `(Range, KItem)` from the Range value `[0, 3)`; `rmK_keys_sorted` at it gives the
    keys of a two-entry range map as a Set value.
  - `cx` (the Range constructor, Range not below KItem): a Range value exists and `RangeBelow`
    fails, so it is no condition every semantics meets.
  - `c0` (no Range constructor, Range not below KItem): `coreOK` holds, so `RangeBelow` holds with
    no subsort `(Range, KItem)`.
  - `patternHooks_ne_rmKeys`, `collPatternHooks_ne_rmKeys` at a map and a set pattern symbol.
  - `rangeKeysOK` (a conjunct of `srReady`): at `cR` from `coreOK`, from `genWf` and by the kernel,
    and `srReady_of`, `SortCtx.range` and the tables' form there; false at `cx`, which `srReady`
    now refuses; false at `cy` (the Range constructor's symbol of result Range at arguments no
    range term has), where `RangeBelow` holds: the decided form is the stronger.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.RangeBelowTest

open KCore ML Faithful Faithful.Model

/-- The configuration `<k> K </k>` with the generated counter. -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- The Range constructor, with Int and Range below KItem. -/
def libR : Lib := { sortsBelowKItem := [Srt.int, Srt.range], ctors := [⟨rangeCtor, [Srt.kitem, Srt.kitem], Srt.range⟩] }

def cR : Semantics :=
  { lib := libR
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

instance : OvlOK cR := .of_nil rfl (by decide +kernel)

theorem sortedOK : cR.sortedOK = true := by decide +kernel
theorem coreOK : cR.coreOK = true := by decide +kernel

theorem fnHyp : FnHyp cR :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

theorem hyp : HypModelCore cR := hypModel_of_fnHyp coreOK fnHyp

/-- `[0, 3)` is a Range value of `cR`. -/
theorem range03 : cR.sortOf (rangeT 0 3) = some Srt.range := by decide +kernel

example : (Srt.range, Srt.kitem) ∈ cR.subsorts := rangeBelow_of_core coreOK 0 3 range03
example : (Srt.range, Srt.kitem) ∈ cR.subsorts := rangeBelow_of_sound (hypSound_of_core coreOK) 0 3 range03
example : (Srt.range, Srt.kitem) ∈ cR.subsorts := rangeBelow_of_model hyp 0 3 range03
example : (Srt.range, Srt.kitem) ∈ cR.subsorts := rangeBelow_of_genWf (by decide +kernel) 0 3 range03

def MK : GroundTerm := rmV [(rangeT 0 3, kint 7), (rangeT 5 7, kint 8)]

/-- `keys` of a two-entry range map, by `rmKeysHook`: the Set of the two injected ranges. -/
example : rmKeysHook [MK] =
    some (.set Srt.set [.inj Srt.range Srt.kitem (rangeT 0 3), .inj Srt.range Srt.kitem (rangeT 5 7)]) := by
  decide +kernel

/-- That Set is a Set value of `cR`, by `rmK_keys_sorted` with `RangeBelow` from `coreOK`. -/
example : cR.sortOf (.set Srt.set [.inj Srt.range Srt.kitem (rangeT 0 3), .inj Srt.range Srt.kitem (rangeT 5 7)]) =
    some Srt.set :=
  rmK_keys_sorted collOf_rangeMap (rangeBelow_of_core coreOK) (ws := [MK]) (by decide +kernel) (by decide +kernel)

/-- The Range constructor with Range not below KItem: a Range value, and `RangeBelow` fails. -/
def cx : Semantics :=
  { sortNames := [], symNames := [], userSorts := [], ctors := [], fns := [], userSubsorts := [],
    pgmSort := Srt.int, rules := [],
    lib := { sortsBelowKItem := [Srt.int], ctors := [⟨rangeCtor, [Srt.kitem, Srt.kitem], Srt.range⟩] } }

theorem cx_not_below : ¬ RangeBelow cx :=
  fun h => absurd (h 0 1 (by decide +kernel)) (by decide +kernel)

/-- No Range constructor, Range not below KItem: `coreOK` holds, so `RangeBelow` does. -/
def c0 : Semantics :=
  { cx with pgmSort := Srt.k, lib := { sortsBelowKItem := [Srt.int] } }

theorem c0_core : c0.coreOK = true := by decide +kernel
example : RangeBelow c0 ∧ (Srt.range, Srt.kitem) ∉ c0.subsorts := ⟨rangeBelow_of_core c0_core, by decide +kernel⟩

example : mapConcat ≠ rmKeys := patternHooks_ne_rmKeys mapConcat (by decide)
example : setConcat ≠ rmKeys := collPatternHooks_ne_rmKeys setConcat (by decide)

/-! `rangeKeysOK`, the decided form `srReady` holds (and `SortCtx.range` reads). -/

theorem keysOK : cR.rangeKeysOK = true := by decide +kernel
example : cR.rangeKeysOK = true := rangeKeysOK_of_core coreOK
example : cR.rangeKeysOK = true := rangeKeysOK_of_genWf (by decide +kernel) (by decide +kernel)
example : (Srt.range, Srt.kitem) ∈ cR.subsorts := rangeBelow_of_keysOK keysOK 0 3 range03
/-- Range is a constructor sort of `cR` (the Range constructor's result), so below KItem. -/
example : (Srt.range, Srt.kitem) ∈ cR.subsorts :=
  rangeKeys_cons_below (by decide +kernel) (by decide +kernel : Srt.range ∈ consSorts cR)
example : genWf cR = true := NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts coreOK).2.1

/-- `srReady` from its five hypotheses, and the Range field of `SortCtx` built from it. -/
theorem srReady : cR.srReady = true :=
  NamesApart.srReady_of (by decide +kernel) (by decide +kernel) sortedOK (by decide +kernel) (by decide +kernel)
example : (Srt.range, Srt.kitem) ∈ cR.subsorts :=
  (sortCtx_of_all sortedOK srReady (Semantics.ovlCase_of_core coreOK)).range 0 3 range03

/-- The tables' form, as the generated `Facts/SrReady` decides it. -/
example : (tables cR).rangeKeysT = true := (rangeKeysT_tables cR).trans keysOK
example : cR.srReadyT (tables cR) = true := by decide +kernel

/-- `srReady` refuses `cx`: its other two conjuncts hold. -/
example : cx.rangeKeysOK = false ∧ cx.srReady = false ∧ nodup (cx.allFns.map (·.label)) = true := by
  decide +kernel

/-- The Range constructor's symbol with result Range and an argument list no range term has:
`RangeBelow` holds, the decided form does not (it is stronger than `RangeBelow`). -/
def cy : Semantics := { cx with lib := { sortsBelowKItem := [Srt.int], ctors := [⟨rangeCtor, [Srt.bool], Srt.range⟩] } }

theorem cy_below : RangeBelow cy := by
  intro a b hs
  exfalso
  have hk' : lookupSig cy.ctorSigs rangeCtor = some ⟨rangeCtor, [Srt.bool], Srt.range⟩ := by decide +kernel
  rcases cy.sortOf_ctor_iff.mp hs with ⟨k, hk, hargs, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · rw [hk'] at hk; cases hk
    have := sortsOf_length hargs
    simp at this
  · rw [hk'] at hn; cases hn
  · rw [hk'] at hn; cases hn
example : cy.rangeKeysOK = false ∧ genWf cy = false := by decide +kernel

end KCore.RangeBelowTest

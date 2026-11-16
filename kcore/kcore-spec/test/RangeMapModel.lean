/-
  RANGEMAP in the model and in the totality of the interpreted symbols, at a semantics `cR` that
  `coreOK` accepts: the configuration `<k> K </k>` with the generated counter, the Range
  constructor, Int and Range below KItem, and no function (so `FnHyp` holds). Run from the package
  root: `lake env lean -j1 test/RangeMapModel.lean`. Kernel-checked (`decide +kernel`).

  - `HypModelCore cR` (`hypModel_of_fnHyp`); a range map value of two entries denotes exactly its
    own element (`den_rmEntries`, its `x :: y :: es` case) and one of one entry (`den_rmEntry`).
  - The seven interpreted RANGEMAP symbols off `partialHooks` have a value at arguments of their
    sorts (`rangeMapHook_total`, `hook_total` at `size` and at `orDefault`), and `partialHooks`
    holds the other seven.
  - The element symbol at `[5, 3)`: a silent point, the result the interpretation's; at `[0, 3)`,
    `hook`'s value under every interpretation.
  - The value model's domain and signature cases with the fourteen entries (`satDomainsGoal`,
    `satSigGoal`), the graphs of `size` and `r|->` at values (`sat_hookGraph`), no junk at RangeMap
    (`sat_collNoJunk`), a range map as one element of its sort (`sat_valElem`); `collAxioms` at
    RangeMap is empty and no range-map symbol is in `patternHooks` or `collPatternHooks`.
  - A definition's own range-map collection: test/RangeMapOwn.lean.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.RangeMapModelTest

open KCore ML Faithful Faithful.Model

/-- The configuration `<k> K </k>` with the generated counter, as ordinary sorts, constructors
and subsorts: the top cell's, its fragment's, the `k` cell's and the counter's. -/
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

/-- `cR` has no function: `FnHyp` holds. -/
theorem fnHyp : FnHyp cR :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_sortedOK sortedOK⟩

theorem hyp : HypModelCore cR := hypModel_of_fnHyp coreOK fnHyp

/-! ## The model at range-map values -/

def e2 : List (GroundTerm × GroundTerm) := [(rangeT 0 3, kint 7), (rangeT 5 7, kint 8)]

/-- `[0,3) ↦ 7, [5,7) ↦ 8` denotes exactly its own element, under every valuation. -/
example (e : Valuation Elem) :
    Sing cR e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries cR (builtinColl .rangeMap) e2))
      (.val (.map Srt.rangeMap e2)) :=
  den_rmEntries hyp e2 (by decide +kernel) (by decide +kernel) e

/-- One entry, `[0,3) ↦ 7`. -/
example (e : Valuation Elem) :
    Sing cR e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntry cR (builtinColl .rangeMap) (rangeT 0 3, kint 7)))
      (.val (.map Srt.rangeMap [(rangeT 0 3, kint 7)])) :=
  den_rmEntry hyp (rangeT 0 3, kint 7) rfl (by decide +kernel) e

/-! ## The element symbol at an improper range -/

/-- `[5, 3) r|-> 7` is a silent point: `hook` gives no value and the text says nothing of one, so
the result is the interpretation's (none under `HookParams.none`); at the proper range `[0, 3)` it
is the one-entry map under every interpretation. Γ determines neither ⊥ nor a value at
`[5, 3) r|-> 7` (`rangeMap_undetermined`, test/SilentPoints.lean). -/
example : hook rmElem [rangeT 5 3, kint 7] = some none ∧ silent rmElem [rangeT 5 3, kint 7] = true ∧
    (cR.withHooks HookParams.none).hookRes rmElem [rangeT 5 3, kint 7] = some none := by decide +kernel

example (H : HookParams) :
    (cR.withHooks H).hookRes rmElem [rangeT 0 3, kint 7] = some (some (rmV [(rangeT 0 3, kint 7)])) :=
  Semantics.hookRes_of_value (rmM_elem rfl)

/-! ## Totality of the interpreted symbols -/

/-- `partialHooks` holds RANGEMAP's seven partial symbols and none of the other seven. -/
example : [rmElem, rmConcat, rmLookup, rmFindRange, rmUpdate, rmRemove, rmRemoveAll].all partialHooks.contains = true ∧
    [rmUnit, rmLookupOrDefault, rmDifference, rmUpdateAll, rmInKeys, rmSize, rmInclusion].all
      (!partialHooks.contains ·) = true := by decide +kernel

theorem shapesOK : cR.shapesOK = true := by decide +kernel

def M : GroundTerm := rmV e2

/-- `orDefault` at a key in no interval, by `rangeMapHook_total`. -/
example : ∃ v, hook rmLookupOrDefault [M, kint 4, kint 0] = some (some v) :=
  rangeMapHook_total shapesOK ⟨rmLookupOrDefault, [Srt.rangeMap, Srt.kitem, Srt.kitem], Srt.kitem⟩
    (by decide) (by decide +kernel) _ (by decide +kernel)

/-- `-RangeMap` of two maps, by `rangeMapHook_total`. -/
example : ∃ v, hook rmDifference [M, rmV [(rangeT 1 6, kint 7)]] = some (some v) :=
  rangeMapHook_total shapesOK ⟨rmDifference, [Srt.rangeMap, Srt.rangeMap], Srt.rangeMap⟩
    (by decide) (by decide +kernel) _ (by decide +kernel)

/-- `size` and `<=RangeMap`, by `hook_total`. -/
example : ∃ v, hook rmSize [M] = some (some v) :=
  hook_total shapesOK ⟨rmSize, [Srt.rangeMap], Srt.int⟩ (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

example : ∃ v, hook rmInclusion [rmV [(rangeT 0 2, kint 7)], M] = some (some v) :=
  hook_total shapesOK ⟨rmInclusion, [Srt.rangeMap, Srt.rangeMap], Srt.bool⟩ (by decide +kernel) (by decide +kernel) _
    (by decide +kernel)

/-! ## The value model's domain and signature cases with the fourteen entries -/

/-- The value model satisfies the domains (the graphs of the fourteen among them) and the
signature (their arities among them) at `cR`. -/
example : SatDomainsGoal cR := satDomainsGoal hyp
example : SatSigGoal cR := satSigGoal hyp

/-- The graph of `size` at `M`: two entries. -/
example : stdI cR ⊧ᴵ (KoreAML.den (symApp cR rmSize (GroundTerm.koreList cR [M])) ≡ den cR (int 2)) :=
  sat_hookGraph hyp (k := ⟨rmSize, [Srt.rangeMap], Srt.int⟩) (r := some (int 2)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The graph of `r|->` at `[0, 3)` and `7`: the one-entry map. -/
example : stdI cR ⊧ᴵ (KoreAML.den (symApp cR rmElem (GroundTerm.koreList cR [rangeT 0 3, kint 7])) ≡
    den cR (rmV [(rangeT 0 3, kint 7)])) :=
  sat_hookGraph hyp (k := ⟨rmElem, [Srt.range, Srt.kitem], Srt.rangeMap⟩) (r := some (rmV [(rangeT 0 3, kint 7)]))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- No junk at RangeMap: every range map value lies in every set closed under the unit, the
element and the concatenation. -/
example : stdI cR ⊧ᴵ collNoJunk cR (builtinColl .rangeMap) := sat_collNoJunk hyp rmM_mem

/-- The range map `M` is one element of RangeMap. -/
example : stdI cR ⊧ᴵ KoreAML.sExists ⟨1⟩ (sortP (cR.sortName Srt.rangeMap)) (den cR M ≡ .evar ⟨1⟩) :=
  sat_valElem hyp (by decide +kernel)

/-- The collection axioms at RangeMap are none (`collAxioms`' `.rangeMap` arm), and no
range-map symbol is a pattern symbol (`patternHooks`, `collPatternHooks`). -/
example : collAxioms cR (builtinColl .rangeMap) = [] := rfl

example : rangeMapHooks.all (fun p => !patternHooks.contains p.1 && !collPatternHooks.contains p.1) = true := by
  decide +kernel

end KCore.RangeMapModelTest

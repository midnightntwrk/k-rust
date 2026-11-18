/-
  The collection laws of `_RangeMap_` and Range's no-junk sentence on the fixture e6-rangemap's
  kompiled text (`f2-examples/e6rm.kompile.kore`, test/TieRangeMap.lean's text), for every
  interpretation H meeting the condition each names.
  Run from the package root: `lake env lean -j1 test/LibEvRangeMapEns.lean`.

  - 68, 69: the right and the left unit of `_RangeMap_` (`M .RangeMap = M`, `.RangeMap M = M`),
    entailed at values (`EntailsAtValues`, direction Ev) for every H, from the library's statement
    (`LibEv.rmUnitR_ev`, `LibEv.rmUnitL_ev`, KcoreSpec/LibEvLawRm.lean): the empty range map
    concatenated with a range map, either way round, is that map, and no silent point is read.
  - 67: associativity, `(M N) P = M (N P)`: entailed at values for every H meeting
    `rangeMapAssocEq` (`law67`, `LibEv.rmAssoc_ev`), the sentence as a condition on the
    interpretation: `_RangeMap_` is silent at two maps with a key in common, where a side is the
    interpretation's value. Every H that gives `_RangeMap_` no value meets it (`law67_none` at
    `HookParams.none`, `law67_lib` at `HookParams.lib`).
  - 152, Range's no-junk sentence `\or{SortRange}(\exists X0:KItem. \exists X1:KItem.
    Range(X0, X1), \bottom)`: entailed by Γ for every H (`nojunk152_entailed`, direction E).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvRangeMapEns

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6rm.kompile.kore"
definition_of defn from "f2-examples/e6rm.kompile.kore"
user_axioms U from "f2-examples/e6rm.kompile.kore" module "E6-RANGEMAP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-! ## The collection laws of `_RangeMap_` (67 to 69) -/

/-- **Associativity (67)**, entailed at values for every H meeting `rangeMapAssocEq`. -/
theorem law67 (H : HookParams) (hA : (cH H).rangeMapAssocEq) :
    EntailsAtValues (cH H) U.ax67 (trS U.ax67).pat := by
  rw [(by decide +kernel : (trS U.ax67).pat = (trAxiom [] [] U.ax67).pat)]
  exact LibEv.rmAssoc_ev (coreOKH H) U.ax67 (by decide +kernel) hA (by decide +kernel)

/-- 67 under `HookParams.none`, which gives `_RangeMap_` no value. -/
theorem law67_none : EntailsAtValues (cH HookParams.none) U.ax67 (trS U.ax67).pat :=
  law67 HookParams.none (rangeMapAssocEq_of_app_none fun _ => rfl)

/-- 67 under `HookParams.lib`. -/
theorem law67_lib : EntailsAtValues (cH HookParams.lib) U.ax67 (trS U.ax67).pat :=
  law67 HookParams.lib (rangeMapAssocEq_lib c)

/-- **The right unit (68)**, entailed at values for every H. -/
theorem law68 (H : HookParams) : EntailsAtValues (cH H) U.ax68 (trS U.ax68).pat := by
  rw [(by decide +kernel : (trS U.ax68).pat = (trAxiom [] [] U.ax68).pat)]
  exact LibEv.rmUnitR_ev (coreOKH H) U.ax68 (by decide +kernel) (shapesOKH H) (by decide +kernel)

/-- **The left unit (69)**, entailed at values for every H. -/
theorem law69 (H : HookParams) : EntailsAtValues (cH H) U.ax69 (trS U.ax69).pat := by
  rw [(by decide +kernel : (trS U.ax69).pat = (trAxiom [] [] U.ax69).pat)]
  exact LibEv.rmUnitL_ev (coreOKH H) U.ax69 (by decide +kernel) (shapesOKH H) (by decide +kernel)

/-! ## Range's no-junk sentence (152) -/

/-- The translation of 152 is Γ's no-junk item of Range, over Range's one generator, the
constructor `RangeMap:Range`. -/
theorem nojunk152_eq : (trS U.ax152).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.range) ((c.gens Srt.range).map (Gen.toK c))).pat := by
  decide +kernel

/-- **E for 152**: Γ entails Range's no-junk sentence, for every H. -/
theorem nojunk152_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax152).pat := by
  intro M _ I hI
  rw [nojunk152_eq]
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.range)
    (show Srt.range ∈ consSorts c by decide +kernel) (show (c.gens Srt.range).isEmpty = false by decide +kernel), rfl⟩)

end KCore.LibEvRangeMapEns

/-- info: 'KCore.LibEvRangeMapEns.law67' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRangeMapEns.law67
/-- info: 'KCore.LibEvRangeMapEns.law68' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRangeMapEns.law68
/-- info: 'KCore.LibEvRangeMapEns.law69' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRangeMapEns.law69
/-- info: 'KCore.LibEvRangeMapEns.nojunk152_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvRangeMapEns.nojunk152_entailed

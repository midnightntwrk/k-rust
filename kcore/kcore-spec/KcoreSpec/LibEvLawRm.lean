/-
  KCore, checked layer: the collection laws of `_RangeMap_` (domains.md 508: `assoc`,
  `unit(.RangeMap)`) at values (`EntailsAtValues`), for every semantics meeting `coreOK` whose
  RangeMap values are range maps (`shapesOK`).

  - The two unit laws `M .RangeMap = M` and `.RangeMap M = M` hold under every interpretation:
    `.RangeMap` is the empty range map, and `hook` concatenates it with any range map, either way
    round, giving that map (`rmConcat_unit`); no silent point is read (`rmUnitR_ev`, `rmUnitL_ev`).
  - Associativity `(M N) P = M (N P)` reads the interpretation: `_RangeMap_` is silent at every
    point (`silentTable`) and `hook` gives no value at two maps with a key in common, so where two of
    the three have one a side is the interpretation's value. The law holds at values wherever
    the interpretation meets `rangeMapAssocEq` (the sentence as a condition on the interpretation,
    a conjunct of `libAdmitted`), and is entailed there (`rmAssoc_ev`); it is met by every
    interpretation that gives `_RangeMap_` no value (`rangeMapAssocEq_of_app_none`), among them
    `HookParams.none` and `HookParams.lib`.
-/
import KcoreSpec.LibEvLaw
import KcoreSpec.RangeMapLaws

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

section
variable {c : Semantics} (hs : c.shapesOK = true) {vars : Vars} {σ : Subst}
  (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
include hs hσ

/-- A substitution of values of the variables' sorts gives a RangeMap variable a range map of
maximal intervals in order. -/
theorem fq_rm_at (i : Nat) {n : String} (hi : vars[i]? = some (n, Srt.rangeMap)) :
    ∃ es, σ.lookup i = some (rmV es) ∧ rangesOK es = true := by
  obtain ⟨v, hv, hsv⟩ := hσ i _ hi
  obtain ⟨es, _, rfl, -⟩ := shape_rangeMap hs hsv
  exact ⟨es, hv, ((rmS_sortOf_map collOf_rangeMap).mp hsv).2.1⟩

end

theorem fhv_rmUnit {c : Semantics} : c.hv rmUnit [] = some (rmV []) :=
  hv_of_value (rmConcat_unit (es := []) rfl).1

/-- `M .RangeMap = M` at every range-map value, under every interpretation. -/
theorem rmUnitR_holds {c : Semantics} (hs : c.shapesOK = true) :
    (lawUnitR rmConcat rmUnit Srt.rangeMap).Holds c := by
  intro σ hσ
  obtain ⟨es, ha, he⟩ := fq_rm_at hs hσ 0 (n := "K") rfl
  fq_law [ha, fhv_rmUnit]
  exact hv_of_value (rmConcat_unit he).2.2

/-- `.RangeMap M = M` at every range-map value, under every interpretation. -/
theorem rmUnitL_holds {c : Semantics} (hs : c.shapesOK = true) :
    (lawUnitL rmConcat rmUnit Srt.rangeMap).Holds c := by
  intro σ hσ
  obtain ⟨es, ha, he⟩ := fq_rm_at hs hσ 0 (n := "K") rfl
  fq_law [ha, fhv_rmUnit]
  exact hv_of_value (rmConcat_unit he).2.1

/-- `(M N) P = M (N P)` at every three range-map values, under every interpretation meeting
`rangeMapAssocEq`. -/
theorem rmAssoc_holds {c : Semantics} (hA : c.rangeMapAssocEq) :
    (lawAssoc rmConcat Srt.rangeMap).Holds c := by
  intro σ hσ
  obtain ⟨m, hm, hsm⟩ := hσ 0 _ rfl
  obtain ⟨n, hn, hsn⟩ := hσ 1 _ rfl
  obtain ⟨p, hp, hsp⟩ := hσ 2 _ rfl
  fq_law [hm, hn, hp]
  have h := hA m n p (by simp only [sortsOf_eq_cons]; exact ⟨hsm, hsn, hsp, rfl⟩)
  cases h1 : c.hv rmConcat [m, n] <;> cases h2 : c.hv rmConcat [n, p] <;>
    simp only [h1, h2, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some] at h ⊢ <;>
    exact h

/-! ### The three laws, entailed at values -/

section
variable {c : Semantics} (h : c.coreOK = true) (ad : KoreAML.AxiomDecl)
  (hsv : ad.ax.sortVars = [KoreAML.Rv])
include h hsv

theorem rmUnitR_ev (hs : c.shapesOK = true)
    (hp : ad.ax.pattern = (lawUnitR rmConcat rmUnit Srt.rangeMap).patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Law.entailed_reg h _ (by decide) (by rfl) (rmUnitR_holds hs) ad hp hsv
theorem rmUnitL_ev (hs : c.shapesOK = true)
    (hp : ad.ax.pattern = (lawUnitL rmConcat rmUnit Srt.rangeMap).patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Law.entailed_reg h _ (by decide) (by rfl) (rmUnitL_holds hs) ad hp hsv
/-- Associativity, entailed at values under every interpretation meeting `rangeMapAssocEq`. -/
theorem rmAssoc_ev (hA : c.rangeMapAssocEq)
    (hp : ad.ax.pattern = (lawAssoc rmConcat Srt.rangeMap).patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Law.entailed_reg h _ (by decide) (by rfl) (rmAssoc_holds hA) ad hp hsv

end

end LibEv

end KCore

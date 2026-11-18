/-
  KCore. A condition's predicate at the sort variable `R`, in the value model.

  The value model at every transition T has what `holds_atR` reads beside the atoms' facts: the
  elements of a well-sorted term of a numbered sort, at a valuation of its variables in their
  sorts, lie in its sort (`termsInSort_stdI`). The variables of such a term have numbered sorts
  (`varOccs_numOpen`), whose elements are the values of those sorts; at values the term denotes
  the values `EvalTerm` gives it (`AtT.tr_term`), which are of its sort (`EvalTerm.sorted_at`).
  `holdsT_atR` is `HoldsT`'s reading of a condition at the sort a valuation gives `R`.
-/
import KcoreSpec.CondCross
import KcoreSpec.HoldsModel

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics} {T : GroundTerm → GroundTerm → Prop}

/-- An element of a sort of the value model is a value of that sort. -/
theorem inSort_valResort {s : Srt} {a : Elem} (h : InSort c s a) : ∃ v, a = .val v ∧ c.sortOf v = some s := by
  cases a with
  | val v => exact ⟨v, rfl, h⟩
  | srt _ => exact h.elim
  | app _ _ => exact h.elim

/-- **The value model at T has `TermsInSort`**, from `HypModelCore`. -/
theorem termsInSort_stdI (h : HypModelCore c) : TermsInSort c (stdI_T c T) := by
  intro vars tbl e t s ht hs hin a ha
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := h.sound
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allClEx hok hsr (OvlOK.ovlCase hno)
  have hlt : ∀ i ∈ varOccs t, i < vars.length := varOccs_lt t ht
  have hget : ∀ i ∈ varOccs t, vars[i]? = some (vars.getD i 0) := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlt i hi)]; rfl
  have hnum : ∀ i ∈ varOccs t, vars.getD i 0 < nRegSorts + c.sortNames.length := fun i hi =>
    varOccs_numOpen h (fun k hk => rhsHead_kernel fns_headsOK hk) (fun _ _ h' => h') t ht hs i hi _ (hget i hi)
  have hval : ∀ i ∈ varOccs t, ∃ v, e.evalEvar (tbl.ev (canonKey c vars i)) = .val v ∧
      c.sortOf v = some (vars.getD i 0) := fun i hi =>
    inSort_valResort ((inhOf_srtOf_stdI (T := T) (tbl := tbl) h (hnum i hi) e _).mp
      (HoldsShape.inhOf_srtOf_inS.mpr (hin i hi)))
  have hvar : ∀ i, i ∈ varOccs t → ∀ m,
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c vars) i)).interpret (stdI_T c T) e m ↔
        ∃ v, (substE c tbl vars e).lookup i = some v ∧ m = .val v := by
    intro i hi m
    obtain ⟨v, hE, -⟩ := hval i hi
    rw [AtT.var_read, substE_lookup (hlt i hi)]
    show m = e.evalEvar (tbl.ev (canonKey c vars i)) ↔ _
    rw [hE]
    constructor
    · rintro rfl; exact ⟨v, rfl, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      rw [← Option.some.inj hw]; rfl
  have hsat : c.WellSortedAt vars (varOccs t) (substE c tbl vars e) := by
    intro i hi s' hs'
    obtain ⟨v, hE, hsv⟩ := hval i hi
    refine ⟨v, by rw [substE_lookup (hlt i hi), hE]; rfl, ?_⟩
    rw [hsv, List.getD_eq_getElem?_getD, hs']; rfl
  obtain ⟨v, hev, rfl⟩ := (AtT.tr_term h hvar
    ((termOK_of_sorted h fns_headsOK ht).monoOpen fun i hi => hi) a).mp ha
  have hv := EvalTerm.sorted_at hsc hev fns_headsOK hsat ht rfl
  exact HoldsShape.inhOf_srtOf_inS.mp ((inhOf_srtOf_stdI (T := T) (tbl := tbl) h hs e _).mpr hv)

/-- **A condition at the sort variable `R` in the value model at any transition T**: `HoldsT`'s
reading, at an element of the sort the valuation gives `R`, through a table holding `R` and the
variables of the pattern at `R`. -/
theorem holdsT_atR (h : HypModelCore c) (p : Cond)
    {vars : List Srt} {P : Nat → Prop} {σ : Subst} {b : Bool} {tbl : KoreAML.VarTable} {e : Valuation Elem}
    (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hP : ∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) (hr : ReadsT c vars P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) KoreAML.R p), k ∈ tbl)
    (hRm : KoreAML.VarKey.sortVar "R" ∈ tbl)
    (hσr : KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))))
    (hh : Holds c vars.length σ p b) (a : Elem)
    (ha : KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) KoreAML.R p)).interpret (stdI_T c T) e a ↔ b = true :=
  HoldsShape.holds_atR (atomFacts_stdI h) (termsInSort_stdI h) (den_of_holdsT h (holds_atT (T := T) h p))
    hok hbd hP (reads_of_readsT h hr) hk hRm (fun _ => Iff.rfl) hσr hh a ha

end Model

end Faithful

end KCore

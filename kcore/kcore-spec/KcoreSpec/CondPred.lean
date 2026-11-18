/-
  KCore. A condition is a predicate: the statement at a definition `coreOK` accepts.

  `cond_pred_transfer`: in a model of `Γ c`, a well-sorted condition's pattern holds at one element
  of the sentence's sort iff at any other (`cond_predAt`, CondPredAt.lean).
-/
import KcoreSpec.CondPredAt
import KcoreSpec.ExSound
import KcoreSpec.FaithfulComplete

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A condition's conjuncts hold at one element of the sentence's sort iff at any other** (R3,
`successor_split_ppCEx`'s `hpred`): in a model of `Γ c` of a definition `coreOK` accepts, for a
well-sorted condition p at a numbered sort S, through a table holding the keys of its pattern's
variables, at a valuation that gives each free variable of p an element of its sort. -/
theorem cond_pred_transfer (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {vars : List Srt} {p : Cond}
    (hok : c.condOK vars p = true) {S : Srt} (hS : S < nRegSorts + c.sortNames.length)
    {tbl : VarTable} {e : Valuation M} {a a' : M}
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl)
    (hf : ∀ i ∈ varOccsCond vars.length p, canonKey c vars i ∈ tbl ∧
      InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i))))
    (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a)
    (ha' : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e a') :
    (∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c S) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) →
      ∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c S) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a' := by
  obtain ⟨-, -, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  obtain ⟨τS, hσS, hτS⟩ := srt_den hI hS
  have hP := cond_predAt hI (defOK hI) (sat_sigItem hI sig_ceilDef) hg hτS hσS p hok hk hf a a'
    ((KoreAML.interp_inhOf_of (hτS tbl e)).mp ha) ((KoreAML.interp_inhOf_of (hτS tbl e)).mp ha')
  intro hall φ hφ
  have hφ' := hφ
  unfold Cond.conj at hφ
  split at hφ
  · cases hφ
  · rw [List.mem_singleton] at hφ
    subst hφ
    exact hP.mp (hall _ hφ')

/-- `cond_pred_transfer` at the configuration sort, in the form of `successor_split_ppCEx`'s `hpred`
with its two hypotheses: the table holds the pattern's keys, and the valuation gives each free
variable of the condition an element of its sort. -/
theorem cond_pred_transfer_top (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {vars : List Srt} {p : Cond}
    (hok : c.condOK vars p = true) :
    ∀ (tbl : VarTable) (e : Valuation M) (a a' : M),
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p), k ∈ tbl) →
      (∀ i ∈ varOccsCond vars.length p, canonKey c vars i ∈ tbl ∧
        InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i)))) →
      (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a →
      (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a' →
      (∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) →
      ∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a' :=
  fun _ _ _ _ hk hf ha ha' => cond_pred_transfer h hI hok top_numbered hk hf ha ha'

end

end Faithful

end KCore

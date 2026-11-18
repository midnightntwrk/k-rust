/-
  KCore. A competitor with a `pre`, in a model of `Γc`: what its `applies` pattern reads.

  `applies` of a rule is `∃x̄'. (lhs ∧ ⌈req = true⌉ ∧ pre)` (`Model.applies_eqPP`), the conjunct
  `pre` the condition's pattern `Cond.kore` where it is not `\top`.

  - `interp_bodyPPI`: the body of `applies` in any interpretation is its left side, its `requires`
    and the conjuncts of its `pre`.
  - `reads_of_agreesAt`: a σ that agrees with a valuation is read at the variables where it gives
    values of their sorts, their keys in the table.
  - `conj_congrPP`: the conjuncts a predicate adds to a sentence read two valuations alike where
    they agree at its free variables.

  The two directions between `NotApplies` and x's element outside `applies` are FamExCEx.lean's
  (`applies_of_values_ppCEx`, `notApplies_of_not_applies_ppCEx`) and SoundCEx.lean's
  (`not_applies_of_notApplies_heldCEx`).
-/
import KcoreSpec.StepValuesPP
import KcoreSpec.AppliesPP

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK VarTable)
open HoldsShape (hasBinder Reads)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

omit [Inhabited M] in
/-- The body of `applies` in any interpretation: its left side, its `requires` and the conjuncts of
its `pre`. -/
theorem interp_bodyPPI {tbl : VarTable} {e : Valuation M} {m : M} (S : Kore.KSort) (p q : Kore.Pattern)
    (vs : List KoreAML.Var) (C : Kore.KSort) (pre : Cond) :
    (KoreAML.tr ⟨tbl, []⟩ (.and S ([p, q] ++ Cond.conj c vs C pre))).interpret I e m ↔
      (KoreAML.tr ⟨tbl, []⟩ p).interpret I e m ∧ (KoreAML.tr ⟨tbl, []⟩ q).interpret I e m ∧
        ∀ φ ∈ Cond.conj c vs C pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e m := by
  by_cases hT : pre.isTop = true
  · simp only [Cond.conj, hT, if_true, List.append_nil]
    rw [tr_and2, KoreAML.interp_sAnd]
    simp
  · have hc : Cond.conj c vs C pre = [Cond.kore c vs C pre] := by simp [Cond.conj, hT]
    rw [hc, List.cons_append, List.cons_append, List.nil_append, tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
    simp

omit [Inhabited M] in
/-- A σ that agrees with a valuation is read at the variables where it gives values of their
sorts, their keys in the table. -/
theorem reads_of_agreesAt {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : VarTable} {e : Valuation M}
    (hag : Agrees c I tbl (canonVars c vars) σ e)
    (hP : ∀ i, P i → i < vars.length ∧ canonKey c vars i ∈ tbl ∧
      ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (vars.getD i 0)) : Reads c I vars P σ tbl e := by
  intro i hi
  obtain ⟨hl, hk, v, hv, hsv⟩ := hP i hi
  exact ⟨hl, hk, v, hv, hsv, hag i v (by rw [canonVars_length]; exact hl) hv⟩

omit [Inhabited M] in
/-- The conjuncts a predicate adds to a sentence read two valuations alike where they agree at its
free variables. -/
theorem conj_congrPP (hD : DefOK I) {vars : List Srt} {p : Cond} (hok : c.condOK vars p = true)
    {tbl : VarTable} {e e' : Valuation M}
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c topCellSort) p), k ∈ tbl)
    (hkeys : ∀ i ∈ varOccsCond vars.length p, canonKey c vars i ∈ tbl)
    (hag : ∀ i ∈ varOccsCond vars.length p,
      e.evalEvar (tbl.ev (canonKey c vars i)) = e'.evalEvar (tbl.ev (canonKey c vars i))) {a : M}
    (hm : ∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e a) :
    ∀ φ ∈ Cond.conj c (canonVars c vars) (srtOf c topCellSort) p, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e' a := by
  intro φ hφ
  by_cases hT : p.isTop = true
  · simp [Cond.conj, hT] at hφ
  · obtain rfl : φ = Cond.kore c (canonVars c vars) (srtOf c topCellSort) p := by simpa [Cond.conj, hT] using hφ
    exact (tr_condKore_twoT hD p hok (fun k hk0 => ⟨hk k hk0, hk k hk0⟩)
      (fun i hi => ⟨hkeys i hi, hkeys i hi, hag i hi⟩) a).mp (hm _ (by simp [Cond.conj, hT]))

end

end Faithful

end KCore
